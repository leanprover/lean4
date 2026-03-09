// Lean compiler output
// Module: Lean.Elab.PatternVar
// Imports: public import Lean.Elab.Arg public import Lean.Elab.MatchAltView public import Init.Syntax import Init.Data.Nat.Linear import Init.Omega
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_Elab_Term_CollectPatternVars_instInhabitedState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_instInhabitedState_default___closed__0 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_instInhabitedState_default___closed__0_value;
extern lean_object* l_Lean_NameSet_empty;
static lean_once_cell_t l_Lean_Elab_Term_CollectPatternVars_instInhabitedState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_instInhabitedState_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_instInhabitedState_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_instInhabitedState;
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t l_Lean_Name_isSuffixOf(lean_object*, lean_object*);
uint8_t l_Lean_Environment_isConstructor(lean_object*, lean_object*);
uint8_t lean_has_match_pattern_attribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Change to "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___lam__0___closed__0_value;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__1_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__3_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__4;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__5_value;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__8___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "Invalid pattern: Expected a constructor or constant marked with `[match_pattern]`"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__1_value;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__2;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Using "};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__4;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " would be valid:"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__5 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__6;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "one of these"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__7 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__8;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__9 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__9_value;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_MessageData_hint(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__9___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Invalid pattern"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__0 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__0_value;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__1;
static lean_once_cell_t l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__2;
static lean_once_cell_t l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__3_spec__4(lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Change argument name `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "` to `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4___lam__0___closed__1_value;
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4___closed__0_value;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___redArg___closed__0;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Invalid argument "};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__1;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__3;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " for function `"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__5;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Replace `"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__6 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__7;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "` with one of the following parameter names:"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__8 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__9;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "Perhaps you meant one of the following parameter names: "};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__10 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__11;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "names"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__12 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__12_value;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__13 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__13_value;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_andList(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_MessageData_orList(lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isDone(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isDone___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_getNextParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_getNextParam___closed__0 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_getNextParam___closed__0_value;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_getNextParam(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0_spec__0___redArg(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_spec__0(lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Invalid pattern: "};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__1;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " arguments to `"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__3;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "`; expected "};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__5;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "To ignore all remaining arguments, use the ellipsis notation `..`"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__6 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__6_value)}};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__7 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__8;
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__9;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Not enough"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__10 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__10_value;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Too many"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__11 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__11_value;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "arguments"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__12 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__12_value;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "argument"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__13 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__13_value;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "explicit "};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__14 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__14_value;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__15 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__15_value;
static const lean_array_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__16 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__16_value;
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__3 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__3_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__4 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__4_value;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__5 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__5_value;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkApp(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isNextArgAccessible(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isNextArgAccessible___boxed(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Invalid pattern variable: Variable name `"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__0 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__1;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` was already used"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__2 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__3;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Invalid pattern variable: Variable name must be atomic, but `"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__4 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__5;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "` has multiple components"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__6 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__7;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "Invalid pattern variable: Identifier expected, but found"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__8 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__9;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables_spec__0___redArg___closed__0_value;
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__1_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__2_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__3_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__4_value;
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__5_value;
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__6_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__19;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__7___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__5___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__17_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__17_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_mapSepElemsM___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_mapSepElemsM___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__17___closed__0 = (const lean_object*)&l_Array_mapSepElemsM___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__17___closed__0_value;
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19(lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__16_spec__21(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__16_spec__21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__16(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__16___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtor___closed__0 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtor___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__0 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "pattern"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processId___closed__0 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processId___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___closed__2_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 154, 97, 179, 232, 94, 186)}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dotIdent"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__0 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 139, 76, 218, 89, 59, 213, 196)}};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__1 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "syntheticHole"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(218, 189, 67, 60, 211, 196, 112, 165)}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__7_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "explicitUniv"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(206, 217, 218, 63, 82, 102, 26, 62)}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__9_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "namedPattern"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__10 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(161, 38, 53, 234, 94, 148, 183, 69)}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__11 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__11_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "binop"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__12 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(47, 253, 231, 222, 243, 42, 73, 191)}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__13 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__13_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unop"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__14 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(68, 253, 109, 39, 185, 175, 169, 133)}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__15 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__15_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "inaccessible"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__16 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__17_value_aux_2),((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__16_value),LEAN_SCALAR_PTR_LITERAL(243, 90, 7, 119, 108, 205, 19, 233)}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__17 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__17_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__18 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__19 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__19_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__20 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__20_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__21 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__21_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scientific"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__22 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__22_value),LEAN_SCALAR_PTR_LITERAL(219, 104, 254, 176, 65, 57, 101, 179)}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__23 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__23_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "char"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__24 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__24_value),LEAN_SCALAR_PTR_LITERAL(43, 243, 213, 66, 253, 140, 152, 232)}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__25 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__25_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__26 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__26_value;
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__27_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__27_value_aux_2),((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__26_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__27 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__27_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "doubleQuotedName"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__28 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__28_value;
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__29_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__29_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__29_value_aux_2),((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__28_value),LEAN_SCALAR_PTR_LITERAL(194, 121, 78, 150, 98, 156, 35, 157)}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__29 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__29_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__30 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__30_value;
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__30_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__31 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__31_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__32 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__32_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__33 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__33_value;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".."};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__4 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__2_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__4_value),LEAN_SCALAR_PTR_LITERAL(81, 102, 39, 227, 176, 252, 65, 103)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__6_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__7_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__8;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__34 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__34_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__35 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__35_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__36 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__36_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "Invalid struct instance pattern: `with` is not allowed in patterns"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__37 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__37_value;
static lean_once_cell_t l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__38;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__39 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__39_value;
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__40_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__40_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__40_value_aux_2),((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__39_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__40 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__40_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__41 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__41_value;
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__42_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__42_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__42_value_aux_2),((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__41_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__42 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__42_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__14___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 114, .m_capacity = 114, .m_length = 113, .m_data = "Invalid pattern: Overloaded notation is only allowed when all alternatives have the same set of pattern variables"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__14___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__14___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__14___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__14___redArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_root_.namedPattern"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__43 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__43_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_once_cell_t l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__44;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_root_"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__45 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__45_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__45_value),LEAN_SCALAR_PTR_LITERAL(184, 175, 53, 50, 212, 152, 178, 8)}};
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__46_value_aux_0),((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(198, 144, 109, 197, 38, 211, 108, 182)}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__46 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__46_value;
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(49, 116, 63, 109, 27, 85, 193, 79)}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__47 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__47_value;
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__47_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__48 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__48_value;
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__48_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__49 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__49_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__50 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__50_value;
static lean_once_cell_t l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__51;
static const lean_ctor_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__50_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__52 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__52_value;
static const lean_string_object l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".("};
static const lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__53 = (const lean_object*)&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__53_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 89, .m_capacity = 89, .m_length = 88, .m_data = "_private.Lean.Elab.PatternVar.0.Lean.Elab.Term.CollectPatternVars.collect.processCtorApp"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__3___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Elab.PatternVar"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__0_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__0;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "namedArgument"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(226, 89, 129, 113, 173, 121, 169, 188)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__3___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ellipsis"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__2 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(101, 52, 71, 179, 21, 116, 195, 217)}};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__3 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__3_value;
lean_object* l_Lean_Elab_Term_expandApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveId_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "_private.Lean.Elab.PatternVar.0.Lean.Elab.Term.CollectPatternVars.collect.pushNewArg"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "Invalid pattern: Expected an identifier in function position, but found"};
static const lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__1 = (const lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__2;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg___closed__1_value;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(31, 220, 207, 232, 230, 163, 41, 26)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "collecting variables at pattern: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_main___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_main___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Term_collectPatternVars___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_collectPatternVars___redArg___closed__0;
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_collectPatternVars___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_collectPatternVars___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_collectPatternVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_collectPatternVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_getPatternVars___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_Lean_Elab_Term_getPatternVars___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Term_getPatternVars___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_getPatternVars___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_getPatternVars___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_getPatternVars___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_getPatternVars___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_getPatternVars___lam__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_getPatternVars___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_getPatternVars___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_getPatternVars___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l_Lean_Elab_Term_getPatternVars___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Term_getPatternVars___lam__0___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Term_getPatternVars___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternVars___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11___redArg___closed__1;
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__0_value;
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__1_value;
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__19_value;
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___closed__0_value;
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___closed__1_value;
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___closed__3_value;
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__2_value;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__8___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__8___redArg___boxed(lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__17___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___redArg___closed__2;
extern lean_object* l_Lean_Elab_pp_macroStack;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___closed__0_value;
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Term_getPatternVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_getPatternVars___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Term_getPatternVars___closed__0 = (const lean_object*)&l_Lean_Elab_Term_getPatternVars___closed__0_value;
lean_object* l_Lean_expandMacros(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_getPatternsVars_spec__1___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_getPatternsVars_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__4___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_getPatternsVars_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_getPatternsVars_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternsVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternsVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_getPatternVarNames_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_getPatternVarNames_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternVarNames(lean_object*);
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedState_default___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_instInhabitedState_default___closed__0));
x_2 = l_Lean_NameSet_empty;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedState_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Elab_Term_CollectPatternVars_instInhabitedState_default___closed__1, &l_Lean_Elab_Term_CollectPatternVars_instInhabitedState_default___closed__1_once, _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedState_default___closed__1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedState(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_instInhabitedState_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_20; uint8_t x_23; 
x_23 = l_Lean_isPrivateName(x_3);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Name_isSuffixOf(x_1, x_3);
if (x_24 == 0)
{
lean_dec(x_3);
lean_dec_ref(x_2);
x_14 = x_5;
goto block_19;
}
else
{
if (x_23 == 0)
{
uint8_t x_25; 
lean_inc(x_3);
lean_inc_ref(x_2);
x_25 = l_Lean_Environment_isConstructor(x_2, x_3);
if (x_25 == 0)
{
uint8_t x_26; 
lean_inc(x_3);
x_26 = lean_has_match_pattern_attribute(x_2, x_3);
x_20 = x_26;
goto block_22;
}
else
{
lean_dec_ref(x_2);
x_20 = x_25;
goto block_22;
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_2);
x_14 = x_5;
goto block_19;
}
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_2);
x_14 = x_5;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
block_22:
{
if (x_20 == 0)
{
lean_dec(x_3);
x_14 = x_5;
goto block_19;
}
else
{
lean_object* x_21; 
x_21 = lean_array_push(x_5, x_3);
x_14 = x_21;
goto block_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___lam__0___closed__0));
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__2));
lean_inc(x_5);
x_9 = lean_mk_syntax_ident(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__4);
x_13 = 0;
x_14 = l_Lean_MessageData_ofConstName(x_5, x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__5));
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_11);
lean_ctor_set(x_19, 3, x_11);
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set(x_19, 5, x_18);
x_20 = 0;
x_21 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_11);
lean_ctor_set(x_21, 2, x_11);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_20);
x_22 = 1;
x_23 = lean_usize_add(x_2, x_22);
x_24 = lean_array_uset(x_7, x_2, x_21);
x_2 = x_23;
x_3 = x_24;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
if (x_11 == 0)
{
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_2);
x_16 = lean_nat_dec_lt(x_4, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_array_fget_borrowed(x_2, x_4);
x_21 = lean_array_fget_borrowed(x_3, x_4);
lean_inc_ref(x_1);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_21);
lean_inc(x_20);
x_22 = lean_apply_12(x_1, x_5, x_20, x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_dec_ref(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_4, x_27);
lean_dec(x_4);
x_4 = x_28;
x_5 = x_25;
x_6 = x_26;
goto _start;
}
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__9___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_37; 
x_13 = lean_ctor_get(x_2, 0);
x_37 = !lean_is_exclusive(x_2);
if (x_37 == 0)
{
x_14 = x_2;
x_15 = x_37;
goto block_36;
}
else
{
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_13);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_4);
if (x_15 == 0)
{
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_19);
x_20 = x_14;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_19);
x_20 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_17, x_17);
if (x_24 == 0)
{
if (x_18 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_4);
if (x_15 == 0)
{
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_25);
x_26 = x_14;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_25);
x_26 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
lean_del_object(x_14);
x_30 = 0;
x_31 = lean_usize_of_nat(x_17);
x_32 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__8___redArg(x_1, x_13, x_30, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_13);
return x_32;
}
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
lean_del_object(x_14);
x_33 = 0;
x_34 = lean_usize_of_nat(x_17);
x_35 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__8___redArg(x_1, x_13, x_33, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_13);
return x_35;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_39);
lean_dec_ref(x_2);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__9___redArg(x_1, x_38, x_39, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__8___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_21; uint8_t x_27; 
x_27 = lean_usize_dec_eq(x_3, x_4);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_array_uget_borrowed(x_2, x_3);
switch (lean_obj_tag(x_28)) {
case 0:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
x_30 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_1);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_30);
lean_inc(x_29);
x_31 = lean_apply_12(x_1, x_5, x_29, x_30, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
x_21 = x_31;
goto block_26;
}
case 1:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_32);
lean_inc_ref(x_1);
x_33 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6___redArg(x_1, x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_21 = x_33;
goto block_26;
}
default: 
{
x_15 = x_5;
x_16 = x_6;
goto block_20;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_6);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
block_20:
{
size_t x_17; size_t x_18; 
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_5 = x_15;
x_6 = x_16;
goto _start;
}
block_26:
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
if (lean_obj_tag(x_22) == 0)
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_1);
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc_ref(x_22);
lean_dec_ref(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_15 = x_24;
x_16 = x_25;
goto block_20;
}
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_1);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__8___redArg(x_1, x_2, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = lean_apply_11(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4___redArg___lam__0___boxed), 13, 1);
lean_closure_set(x_12, 0, x_2);
x_13 = lean_box(0);
x_14 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6___redArg(x_12, x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_4);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 2);
lean_inc(x_18);
lean_dec_ref(x_3);
lean_inc_ref(x_1);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_19 = lean_apply_11(x_1, x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_dec_ref(x_20);
lean_dec(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_2 = x_22;
x_3 = x_18;
x_4 = x_23;
goto _start;
}
}
else
{
lean_dec(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__5___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_3, x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_array_uget_borrowed(x_2, x_3);
x_17 = lean_box(0);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_16);
lean_inc_ref(x_1);
x_18 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__3___redArg(x_1, x_17, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_dec_ref(x_19);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_1);
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_3 = x_24;
x_5 = x_21;
x_6 = x_22;
goto _start;
}
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_1);
return x_18;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_6);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__5___redArg(x_1, x_2, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_1);
x_14 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get_size(x_14);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec_ref(x_14);
x_18 = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4___redArg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_box(0);
x_20 = lean_nat_dec_le(x_16, x_16);
if (x_20 == 0)
{
if (x_17 == 0)
{
lean_object* x_21; 
lean_dec_ref(x_14);
x_21 = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4___redArg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_16);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_2);
x_24 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__5___redArg(x_2, x_14, x_22, x_23, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_14);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4___redArg(x_13, x_2, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_28;
}
}
else
{
lean_dec_ref(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_24;
}
}
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_16);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_2);
x_31 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__5___redArg(x_2, x_14, x_29, x_30, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_14);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_dec_ref(x_32);
lean_dec_ref(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4___redArg(x_13, x_2, x_34, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_35;
}
}
else
{
lean_dec_ref(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__7));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_10 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__2, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__2_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__2);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_82 = lean_ctor_get(x_1, 0);
x_83 = l_Lean_Syntax_getId(x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_118; 
lean_dec_ref(x_1);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_110 = l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1___redArg(x_10, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_111 = lean_ctor_get(x_110, 0);
x_118 = !lean_is_exclusive(x_110);
if (x_118 == 0)
{
x_112 = x_110;
x_113 = x_118;
goto block_117;
}
else
{
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_box(0);
x_113 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_114; 
if (x_113 == 0)
{
x_114 = x_112;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_111);
x_114 = x_116;
goto block_115;
}
block_115:
{
return x_114;
}
}
}
else
{
x_84 = x_2;
x_85 = x_3;
x_86 = x_4;
x_87 = x_5;
x_88 = x_6;
x_89 = x_7;
x_90 = x_8;
goto block_109;
}
block_109:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_st_ref_get(x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc_ref(x_92);
lean_dec(x_91);
lean_inc_ref(x_92);
x_93 = lean_alloc_closure((void*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___lam__0___boxed), 13, 2);
lean_closure_set(x_93, 0, x_83);
lean_closure_set(x_93, 1, x_92);
x_94 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__9));
x_95 = l_Lean_Environment_constants(x_92);
lean_inc(x_90);
lean_inc_ref(x_89);
lean_inc(x_88);
lean_inc_ref(x_87);
lean_inc(x_86);
lean_inc_ref(x_85);
lean_inc(x_84);
x_96 = l_Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2___redArg(x_95, x_93, x_94, x_84, x_85, x_86, x_87, x_88, x_89, x_90);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec_ref(x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_61 = x_85;
x_62 = x_90;
x_63 = x_87;
x_64 = x_88;
x_65 = x_86;
x_66 = x_84;
x_67 = x_89;
x_68 = x_98;
goto block_81;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
lean_dec_ref(x_97);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_61 = x_85;
x_62 = x_90;
x_63 = x_87;
x_64 = x_88;
x_65 = x_86;
x_66 = x_84;
x_67 = x_89;
x_68 = x_100;
goto block_81;
}
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_108; 
lean_dec(x_90);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec_ref(x_1);
x_101 = lean_ctor_get(x_96, 0);
x_108 = !lean_is_exclusive(x_96);
if (x_108 == 0)
{
x_102 = x_96;
x_103 = x_108;
goto block_107;
}
else
{
lean_inc(x_101);
lean_dec(x_96);
x_102 = lean_box(0);
x_103 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_104; 
if (x_103 == 0)
{
x_104 = x_102;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_101);
x_104 = x_106;
goto block_105;
}
block_105:
{
return x_104;
}
}
}
}
}
else
{
lean_object* x_119; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1___redArg(x_10, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_119;
}
block_41:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
lean_dec(x_18);
lean_dec_ref(x_16);
lean_dec(x_15);
x_20 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__4, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__4_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__4);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__6, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__6_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__6);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_array_size(x_11);
x_25 = 0;
x_26 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0(x_24, x_25, x_11);
x_27 = lean_box(0);
x_28 = 0;
lean_inc(x_14);
lean_inc_ref(x_13);
x_29 = l_Lean_MessageData_hint(x_23, x_26, x_1, x_27, x_28, x_13, x_14);
lean_dec_ref(x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_10);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1___redArg(x_31, x_17, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_17);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec_ref(x_17);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
x_33 = lean_ctor_get(x_29, 0);
x_40 = !lean_is_exclusive(x_29);
if (x_40 == 0)
{
x_34 = x_29;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
block_60:
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_array_get_size(x_42);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_dec_eq(x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__8, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__8_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__8);
x_11 = x_42;
x_12 = x_47;
x_13 = x_48;
x_14 = x_49;
x_15 = x_45;
x_16 = x_44;
x_17 = x_46;
x_18 = x_43;
x_19 = x_53;
goto block_41;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__4);
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_array_fget_borrowed(x_42, x_55);
lean_inc(x_56);
x_57 = l_Lean_MessageData_ofName(x_56);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_54);
x_11 = x_42;
x_12 = x_47;
x_13 = x_48;
x_14 = x_49;
x_15 = x_45;
x_16 = x_44;
x_17 = x_46;
x_18 = x_43;
x_19 = x_59;
goto block_41;
}
}
block_81:
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_array_get_size(x_68);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_nat_dec_eq(x_69, x_70);
if (x_71 == 0)
{
x_42 = x_68;
x_43 = x_66;
x_44 = x_61;
x_45 = x_65;
x_46 = x_63;
x_47 = x_64;
x_48 = x_67;
x_49 = x_62;
goto block_60;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
lean_dec_ref(x_68);
lean_dec(x_66);
lean_dec(x_65);
lean_dec_ref(x_61);
lean_dec(x_1);
x_72 = l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1___redArg(x_10, x_63, x_64, x_67, x_62);
lean_dec(x_62);
lean_dec_ref(x_67);
lean_dec(x_64);
lean_dec_ref(x_63);
x_73 = lean_ctor_get(x_72, 0);
x_80 = !lean_is_exclusive(x_72);
if (x_80 == 0)
{
x_74 = x_72;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1___redArg(x_2, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__5___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__5(x_1, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6___redArg(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6___redArg(x_4, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6___redArg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__8___redArg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__8___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_20 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__8(x_1, x_2, x_3, x_4, x_5, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; 
x_19 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__9___redArg(x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__9___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
lean_object* x_19; 
x_19 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__2_spec__4_spec__5_spec__6_spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_19;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg___closed__1, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg___closed__1_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg___closed__1);
x_7 = l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1___redArg(x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg(x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__1, &l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__1_once, _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = lean_obj_once(&l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__2, &l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__2_once, _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__2);
x_3 = lean_unsigned_to_nat(0u);
x_4 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__0));
x_5 = 0;
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_4);
lean_ctor_set(x_8, 3, x_3);
lean_ctor_set(x_8, 4, x_4);
lean_ctor_set(x_8, 5, x_2);
lean_ctor_set(x_8, 6, x_1);
lean_ctor_set(x_8, 7, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*8, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 1, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__3, &l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__3_once, _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__3_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = lean_ctor_get(x_11, 0);
x_13 = l_Lean_Name_hasMacroScopes(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_inc(x_12);
x_14 = lean_array_push(x_4, x_12);
x_5 = x_14;
goto block_9;
}
else
{
x_5 = x_4;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__3_spec__4(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__9));
x_5 = lean_nat_dec_lt(x_2, x_3);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_le(x_3, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_2, x_6);
if (x_8 == 0)
{
return x_4;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_2);
x_10 = lean_usize_of_nat(x_6);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__3_spec__4(x_1, x_9, x_10, x_4);
return x_11;
}
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_usize_of_nat(x_2);
x_13 = lean_usize_of_nat(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__3_spec__4(x_1, x_12, x_13, x_4);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4___lam__0___closed__0));
x_7 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_5, x_2);
x_8 = lean_string_append(x_6, x_7);
lean_dec_ref(x_7);
x_9 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4___lam__0___closed__1));
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_4);
x_12 = lean_string_append(x_11, x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4___lam__0(x_1, x_5, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_5, x_4, x_8);
lean_inc(x_7);
x_10 = l_Lean_Name_toString(x_7, x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__3));
x_13 = lean_box(x_6);
lean_inc_ref(x_1);
x_14 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4___lam__0___boxed), 4, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_12);
x_15 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_7, x_6);
x_16 = lean_string_append(x_12, x_15);
lean_dec_ref(x_15);
x_17 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4___closed__0));
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_14);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_20);
lean_ctor_set(x_22, 4, x_20);
lean_ctor_set(x_22, 5, x_21);
lean_inc(x_2);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_2);
x_24 = 0;
x_25 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_24);
x_26 = 1;
x_27 = lean_usize_add(x_4, x_26);
x_28 = lean_array_uset(x_9, x_4, x_25);
x_4 = x_27;
x_5 = x_28;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
if (x_11 == 0)
{
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__2___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___redArg___closed__0(void) {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(1723u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_20; 
x_20 = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___redArg___closed__0);
x_5 = x_20;
goto block_19;
}
else
{
uint64_t x_21; 
x_21 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_5 = x_21;
goto block_19;
}
block_19:
{
uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0_spec__0___redArg(x_2, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 5);
x_13 = lean_array_uget_borrowed(x_2, x_3);
x_14 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___redArg(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_inc(x_13);
x_15 = lean_array_push(x_5, x_13);
x_6 = x_15;
goto block_10;
}
else
{
x_6 = x_5;
goto block_10;
}
}
else
{
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__6(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__4);
x_9 = l_Lean_MessageData_ofName(x_5);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_7, x_2, x_11);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__5(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_5 = lean_array_uget_borrowed(x_3, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__4);
x_10 = l_Lean_MessageData_ofName(x_6);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_15 = lean_array_uset(x_8, x_2, x_12);
x_2 = x_14;
x_3 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__10));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_72; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 4);
x_10 = lean_array_size(x_9);
x_11 = 0;
lean_inc_ref(x_9);
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__1(x_10, x_11, x_9);
x_13 = lean_array_to_list(x_12);
x_36 = l_List_lengthTR___redArg(x_13);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_dec_eq(x_36, x_37);
lean_dec(x_36);
x_39 = 1;
if (x_38 == 0)
{
lean_object* x_89; 
x_89 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__12));
x_72 = x_89;
goto block_88;
}
else
{
lean_object* x_90; 
x_90 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__13));
x_72 = x_90;
goto block_88;
}
block_35:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_20 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__1, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__1_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__1);
x_21 = l_Lean_stringToMessageData(x_14);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__3, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__3_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__3);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_MessageData_andList(x_13);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__5, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__5_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__5);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_MessageData_ofSyntax(x_7);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__4);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_15);
x_34 = l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__2___redArg(x_33, x_16, x_17, x_18, x_19);
lean_dec(x_19);
lean_dec_ref(x_18);
return x_34;
}
block_71:
{
lean_object* x_45; 
x_45 = l_Lean_Syntax_getHeadInfo(x_40);
if (lean_obj_tag(x_45) == 0)
{
size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_45);
x_46 = lean_array_size(x_44);
x_47 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__4(x_42, x_40, x_46, x_11, x_44);
x_48 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__7, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__7_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__7);
x_49 = l_Lean_MessageData_ofName(x_43);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__9, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__9_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__9);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_box(0);
lean_inc(x_5);
lean_inc_ref(x_4);
x_54 = l_Lean_MessageData_hint(x_52, x_47, x_53, x_53, x_39, x_4, x_5);
lean_dec_ref(x_47);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_14 = x_41;
x_15 = x_55;
x_16 = x_2;
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
goto block_35;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
lean_dec_ref(x_41);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
x_56 = lean_ctor_get(x_54, 0);
x_63 = !lean_is_exclusive(x_54);
if (x_63 == 0)
{
x_57 = x_54;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_box(0);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
if (x_58 == 0)
{
x_59 = x_57;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_56);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
else
{
size_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_40);
x_64 = lean_array_size(x_44);
x_65 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__5(x_64, x_11, x_44);
x_66 = lean_array_to_list(x_65);
x_67 = l_Lean_MessageData_orList(x_66);
x_68 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__11, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__11_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__11);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = l_Lean_MessageData_hint_x27(x_69);
x_14 = x_41;
x_15 = x_70;
x_16 = x_2;
x_17 = x_3;
x_18 = x_4;
x_19 = x_5;
goto block_35;
}
}
block_88:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_array_fget(x_9, x_73);
x_75 = lean_ctor_get(x_74, 0);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
x_77 = lean_array_get_size(x_8);
x_78 = l_Array_filterMapM___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__3(x_8, x_73, x_77);
x_79 = l_Lean_Syntax_getArg(x_75, x_37);
x_80 = lean_array_get_size(x_78);
x_81 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg___closed__9));
x_82 = lean_nat_dec_lt(x_73, x_80);
if (x_82 == 0)
{
lean_dec_ref(x_78);
lean_dec_ref(x_1);
x_40 = x_79;
x_41 = x_72;
x_42 = x_74;
x_43 = x_76;
x_44 = x_81;
goto block_71;
}
else
{
uint8_t x_83; 
x_83 = lean_nat_dec_le(x_80, x_80);
if (x_83 == 0)
{
if (x_82 == 0)
{
lean_dec_ref(x_78);
lean_dec_ref(x_1);
x_40 = x_79;
x_41 = x_72;
x_42 = x_74;
x_43 = x_76;
x_44 = x_81;
goto block_71;
}
else
{
size_t x_84; lean_object* x_85; 
x_84 = lean_usize_of_nat(x_80);
x_85 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__6(x_1, x_78, x_11, x_84, x_81);
lean_dec_ref(x_78);
lean_dec_ref(x_1);
x_40 = x_79;
x_41 = x_72;
x_42 = x_74;
x_43 = x_76;
x_44 = x_85;
goto block_71;
}
}
else
{
size_t x_86; lean_object* x_87; 
x_86 = lean_usize_of_nat(x_80);
x_87 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__6(x_1, x_78, x_11, x_86, x_81);
lean_dec_ref(x_78);
lean_dec_ref(x_1);
x_40 = x_79;
x_41 = x_72;
x_42 = x_74;
x_43 = x_76;
x_44 = x_87;
goto block_71;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg(x_2, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__2___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isDone(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_1, 3);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_le(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isDone___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isDone(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_getNextParam(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_23; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*8 + 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get(x_1, 4);
x_9 = lean_ctor_get(x_1, 5);
x_10 = lean_ctor_get(x_1, 6);
x_11 = lean_ctor_get(x_1, 7);
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
x_12 = x_1;
x_13 = x_23;
goto block_22;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_getNextParam___closed__0));
x_15 = lean_array_get(x_14, x_6, x_7);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_7, x_16);
lean_dec(x_7);
if (x_13 == 0)
{
lean_ctor_set(x_12, 3, x_17);
x_18 = x_12;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_3);
lean_ctor_set(x_21, 2, x_6);
lean_ctor_set(x_21, 3, x_17);
lean_ctor_set(x_21, 4, x_8);
lean_ctor_set(x_21, 5, x_9);
lean_ctor_set(x_21, 6, x_10);
lean_ctor_set(x_21, 7, x_11);
lean_ctor_set_uint8(x_21, sizeof(void*)*8, x_4);
lean_ctor_set_uint8(x_21, sizeof(void*)*8 + 1, x_5);
x_18 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_31; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_31 = !lean_is_exclusive(x_2);
if (x_31 == 0)
{
x_6 = x_2;
x_7 = x_31;
goto block_30;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_8; uint64_t x_9; 
x_8 = lean_array_get_size(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint64_t x_28; 
x_28 = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___redArg___closed__0);
x_9 = x_28;
goto block_27;
}
else
{
uint64_t x_29; 
x_29 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_9 = x_29;
goto block_27;
}
block_27:
{
uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_1, x_20);
lean_inc(x_21);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_21);
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_21);
x_22 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_23; 
x_23 = lean_array_uset(x_1, x_20, x_22);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0_spec__0_spec__1_spec__3___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0_spec__0_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_45; 
x_45 = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___redArg___closed__0);
x_7 = x_45;
goto block_44;
}
else
{
uint64_t x_46; 
x_46 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_7 = x_46;
goto block_44;
}
block_44:
{
uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget_borrowed(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0_spec__0___redArg(x_2, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; uint8_t x_41; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_41 = !lean_is_exclusive(x_1);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_1, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_1, 0);
lean_dec(x_43);
x_21 = x_1;
x_22 = x_41;
goto block_40;
}
else
{
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
lean_inc(x_19);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_19);
x_26 = lean_array_uset(x_5, x_18, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_24, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0_spec__0___redArg(x_26);
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_33);
lean_ctor_set(x_21, 0, x_24);
x_34 = x_21;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
lean_object* x_37; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_26);
lean_ctor_set(x_21, 0, x_24);
x_37 = x_21;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_26);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_name_eq(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__1___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__1___redArg(lean_object* x_1) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isDone(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_4 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_getNextParam(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
x_11 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 1);
x_12 = lean_ctor_get(x_6, 2);
x_13 = lean_ctor_get(x_6, 3);
x_14 = lean_ctor_get(x_6, 4);
x_15 = lean_ctor_get(x_6, 5);
x_16 = lean_ctor_get(x_6, 6);
x_17 = lean_ctor_get(x_6, 7);
lean_inc(x_7);
x_18 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_18, 0, x_7);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), x_18, x_14, x_19);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; uint8_t x_22; uint8_t x_32; 
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_9);
lean_inc(x_8);
x_32 = !lean_is_exclusive(x_6);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_6, 7);
lean_dec(x_33);
x_34 = lean_ctor_get(x_6, 6);
lean_dec(x_34);
x_35 = lean_ctor_get(x_6, 5);
lean_dec(x_35);
x_36 = lean_ctor_get(x_6, 4);
lean_dec(x_36);
x_37 = lean_ctor_get(x_6, 3);
lean_dec(x_37);
x_38 = lean_ctor_get(x_6, 2);
lean_dec(x_38);
x_39 = lean_ctor_get(x_6, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_6, 0);
lean_dec(x_40);
x_21 = x_6;
x_22 = x_32;
goto block_31;
}
else
{
lean_dec(x_6);
x_21 = lean_box(0);
x_22 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec_ref(x_20);
x_24 = l_Array_eraseIdx___redArg(x_14, x_23);
x_25 = lean_box(0);
x_26 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0___redArg(x_15, x_7, x_25);
if (x_22 == 0)
{
lean_ctor_set(x_21, 5, x_26);
lean_ctor_set(x_21, 4, x_24);
x_27 = x_21;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_9);
lean_ctor_set(x_30, 2, x_12);
lean_ctor_set(x_30, 3, x_13);
lean_ctor_set(x_30, 4, x_24);
lean_ctor_set(x_30, 5, x_26);
lean_ctor_set(x_30, 6, x_16);
lean_ctor_set(x_30, 7, x_17);
lean_ctor_set_uint8(x_30, sizeof(void*)*8, x_10);
lean_ctor_set_uint8(x_30, sizeof(void*)*8 + 1, x_11);
x_27 = x_30;
goto block_29;
}
block_29:
{
x_1 = x_27;
goto _start;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_7);
x_1 = x_6;
goto _start;
}
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_1);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__1___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__1___redArg(x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_24; 
x_11 = lean_ctor_get(x_10, 0);
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
x_12 = x_10;
x_13 = x_24;
goto block_23;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 4);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_del_object(x_12);
x_18 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg(x_11, x_5, x_6, x_7, x_8);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
x_19 = lean_box(0);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_19);
x_20 = x_12;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_dec(x_8);
lean_dec_ref(x_7);
x_25 = lean_ctor_get(x_10, 0);
x_32 = !lean_is_exclusive(x_10);
if (x_32 == 0)
{
x_26 = x_10;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_10);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__1___redArg(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0_spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0_spec__0_spec__1_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = lean_ctor_get(x_11, 1);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_BinderInfo_isExplicit(x_13);
if (x_14 == 0)
{
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_15; 
lean_inc(x_11);
x_15 = lean_array_push(x_4, x_11);
x_5 = x_15;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__7));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__8, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__8_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__8);
x_2 = l_Lean_MessageData_hint_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_76; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_1, 4);
if (x_12 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_91 = lean_unsigned_to_nat(0u);
x_92 = lean_array_get_size(x_13);
x_93 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__16));
x_94 = lean_nat_dec_lt(x_91, x_92);
if (x_94 == 0)
{
x_76 = x_93;
goto block_90;
}
else
{
uint8_t x_95; 
x_95 = lean_nat_dec_le(x_92, x_92);
if (x_95 == 0)
{
if (x_94 == 0)
{
x_76 = x_93;
goto block_90;
}
else
{
size_t x_96; size_t x_97; lean_object* x_98; 
x_96 = 0;
x_97 = lean_usize_of_nat(x_92);
x_98 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_spec__0(x_13, x_96, x_97, x_93);
x_76 = x_98;
goto block_90;
}
}
else
{
size_t x_99; size_t x_100; lean_object* x_101; 
x_99 = 0;
x_100 = lean_usize_of_nat(x_92);
x_101 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_spec__0(x_13, x_99, x_100, x_93);
x_76 = x_101;
goto block_90;
}
}
}
else
{
lean_inc_ref(x_13);
x_76 = x_13;
goto block_90;
}
block_46:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_23 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__1, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__1_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__1);
x_24 = l_Lean_stringToMessageData(x_22);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__3, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__3_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__3);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_MessageData_ofSyntax(x_11);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__5, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__5_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__5);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Nat_reprFast(x_20);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_MessageData_ofFormat(x_33);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__3, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__3_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__3);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_stringToMessageData(x_18);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_stringToMessageData(x_21);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
if (x_2 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__9, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__9_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__9);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1___redArg(x_43, x_16, x_19, x_17, x_15);
lean_dec(x_15);
lean_dec_ref(x_17);
return x_44;
}
else
{
lean_object* x_45; 
x_45 = l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1___redArg(x_41, x_16, x_19, x_17, x_15);
lean_dec(x_15);
lean_dec_ref(x_17);
return x_45;
}
}
block_56:
{
if (x_2 == 0)
{
lean_object* x_54; 
x_54 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__10));
x_15 = x_48;
x_16 = x_47;
x_17 = x_49;
x_18 = x_50;
x_19 = x_51;
x_20 = x_52;
x_21 = x_53;
x_22 = x_54;
goto block_46;
}
else
{
lean_object* x_55; 
x_55 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__11));
x_15 = x_48;
x_16 = x_47;
x_17 = x_49;
x_18 = x_50;
x_19 = x_51;
x_20 = x_52;
x_21 = x_53;
x_22 = x_55;
goto block_46;
}
}
block_67:
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_dec_eq(x_61, x_63);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__12));
x_47 = x_58;
x_48 = x_57;
x_49 = x_59;
x_50 = x_62;
x_51 = x_60;
x_52 = x_61;
x_53 = x_65;
goto block_56;
}
else
{
lean_object* x_66; 
x_66 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__13));
x_47 = x_58;
x_48 = x_57;
x_49 = x_59;
x_50 = x_62;
x_51 = x_60;
x_52 = x_61;
x_53 = x_66;
goto block_56;
}
}
block_75:
{
if (x_12 == 0)
{
lean_object* x_73; 
x_73 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__14));
x_57 = x_72;
x_58 = x_69;
x_59 = x_71;
x_60 = x_70;
x_61 = x_68;
x_62 = x_73;
goto block_67;
}
else
{
lean_object* x_74; 
x_74 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__15));
x_57 = x_72;
x_58 = x_69;
x_59 = x_71;
x_60 = x_70;
x_61 = x_68;
x_62 = x_74;
goto block_67;
}
}
block_90:
{
lean_object* x_77; 
x_77 = lean_array_get_size(x_76);
lean_dec_ref(x_76);
if (x_2 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_array_get_size(x_14);
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_nat_dec_eq(x_78, x_79);
if (x_80 == 0)
{
lean_object* x_81; 
lean_inc(x_9);
lean_inc_ref(x_8);
x_81 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_81) == 0)
{
lean_dec_ref(x_81);
x_68 = x_77;
x_69 = x_6;
x_70 = x_7;
x_71 = x_8;
x_72 = x_9;
goto block_75;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_89; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
x_82 = lean_ctor_get(x_81, 0);
x_89 = !lean_is_exclusive(x_81);
if (x_89 == 0)
{
x_83 = x_81;
x_84 = x_89;
goto block_88;
}
else
{
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_box(0);
x_84 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_85; 
if (x_84 == 0)
{
x_85 = x_83;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_82);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
}
}
else
{
lean_dec_ref(x_1);
x_68 = x_77;
x_69 = x_6;
x_70 = x_7;
x_71 = x_8;
x_72 = x_9;
goto block_75;
}
}
else
{
lean_dec_ref(x_1);
x_68 = x_77;
x_69 = x_6;
x_70 = x_7;
x_71 = x_8;
x_72 = x_9;
goto block_75;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
x_13 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_24; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_ctor_get(x_1, 6);
x_13 = lean_ctor_get(x_1, 7);
x_24 = l_List_isEmpty___redArg(x_12);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; 
x_25 = 1;
x_26 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg(x_1, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_array_get_size(x_11);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_eq(x_27, x_28);
if (x_29 == 0)
{
if (x_24 == 0)
{
lean_inc_ref(x_13);
lean_inc(x_10);
lean_dec(x_8);
lean_dec_ref(x_1);
x_14 = x_24;
goto block_23;
}
else
{
lean_object* x_30; 
x_30 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg(x_1, x_5, x_6, x_7, x_8);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_inc_ref(x_13);
lean_inc(x_10);
lean_dec(x_8);
lean_dec_ref(x_1);
x_31 = 0;
x_14 = x_31;
goto block_23;
}
}
block_23:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_7, 5);
lean_inc(x_15);
lean_dec_ref(x_7);
x_16 = l_Lean_SourceInfo_fromRef(x_15, x_14);
lean_dec(x_15);
x_17 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__4));
x_18 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__5));
lean_inc(x_16);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Syntax_node2(x_16, x_17, x_19, x_10);
x_21 = l_Lean_Syntax_mkApp(x_20, x_13);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isNextArgAccessible(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_ctor_get(x_1, 3);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_7 = lean_array_fget_borrowed(x_3, x_4);
x_8 = lean_ctor_get(x_7, 1);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_BinderInfo_isExplicit(x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_ctor_get(x_11, 3);
x_14 = lean_nat_dec_le(x_13, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isNextArgAccessible___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isNextArgAccessible(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_32; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 2);
x_11 = lean_ctor_get(x_5, 3);
x_12 = lean_ctor_get(x_5, 4);
x_13 = lean_ctor_get(x_5, 5);
x_14 = lean_ctor_get(x_5, 6);
x_15 = lean_ctor_get(x_5, 7);
x_16 = lean_ctor_get(x_5, 8);
x_17 = lean_ctor_get(x_5, 9);
x_18 = lean_ctor_get(x_5, 10);
x_19 = lean_ctor_get(x_5, 11);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*14);
x_21 = lean_ctor_get(x_5, 12);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*14 + 1);
x_23 = lean_ctor_get(x_5, 13);
x_32 = !lean_is_exclusive(x_5);
if (x_32 == 0)
{
x_24 = x_5;
x_25 = x_32;
goto block_31;
}
else
{
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_5);
x_24 = lean_box(0);
x_25 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_replaceRef(x_1, x_13);
lean_dec(x_13);
if (x_25 == 0)
{
lean_ctor_set(x_24, 5, x_26);
x_27 = x_24;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_9);
lean_ctor_set(x_30, 2, x_10);
lean_ctor_set(x_30, 3, x_11);
lean_ctor_set(x_30, 4, x_12);
lean_ctor_set(x_30, 5, x_26);
lean_ctor_set(x_30, 6, x_14);
lean_ctor_set(x_30, 7, x_15);
lean_ctor_set(x_30, 8, x_16);
lean_ctor_set(x_30, 9, x_17);
lean_ctor_set(x_30, 10, x_18);
lean_ctor_set(x_30, 11, x_19);
lean_ctor_set(x_30, 12, x_21);
lean_ctor_set(x_30, 13, x_23);
lean_ctor_set_uint8(x_30, sizeof(void*)*14, x_20);
lean_ctor_set_uint8(x_30, sizeof(void*)*14 + 1, x_22);
x_27 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_28; 
x_28 = l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1___redArg(x_2, x_3, x_4, x_27, x_6);
lean_dec_ref(x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_81; 
x_81 = l_Lean_Syntax_isIdent(x_1);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_94; 
x_82 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__9, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__9_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__9);
lean_inc(x_1);
x_83 = l_Lean_MessageData_ofSyntax(x_1);
x_84 = l_Lean_indentD(x_83);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar_spec__0___redArg(x_1, x_85, x_5, x_6, x_7, x_8);
lean_dec(x_1);
x_87 = lean_ctor_get(x_86, 0);
x_94 = !lean_is_exclusive(x_86);
if (x_94 == 0)
{
x_88 = x_86;
x_89 = x_94;
goto block_93;
}
else
{
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_box(0);
x_89 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_90; 
if (x_89 == 0)
{
x_90 = x_88;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_87);
x_90 = x_92;
goto block_91;
}
block_91:
{
return x_90;
}
}
}
else
{
x_58 = x_2;
x_59 = x_5;
x_60 = x_6;
x_61 = x_7;
x_62 = x_8;
goto block_80;
}
block_26:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_25; 
x_12 = lean_st_ref_take(x_11);
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_ctor_get(x_12, 1);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
x_15 = x_12;
x_16 = x_25;
goto block_24;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Lean_NameSet_insert(x_13, x_10);
lean_inc(x_1);
x_18 = lean_array_push(x_14, x_1);
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_18);
lean_ctor_set(x_15, 0, x_17);
x_19 = x_15;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_18);
x_19 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_st_ref_set(x_11, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
}
}
block_57:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_55; 
x_33 = lean_st_ref_get(x_28);
x_34 = lean_ctor_get(x_33, 0);
x_55 = !lean_is_exclusive(x_33);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_33, 1);
lean_dec(x_56);
x_35 = x_33;
x_36 = x_55;
goto block_54;
}
else
{
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = x_55;
goto block_54;
}
block_54:
{
uint8_t x_37; 
x_37 = l_Lean_NameSet_contains(x_34, x_27);
lean_dec(x_34);
if (x_37 == 0)
{
lean_del_object(x_35);
lean_dec_ref(x_31);
x_10 = x_27;
x_11 = x_28;
goto block_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_38 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__1, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__1_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__1);
x_39 = l_Lean_MessageData_ofName(x_27);
if (x_36 == 0)
{
lean_ctor_set_tag(x_35, 7);
lean_ctor_set(x_35, 1, x_39);
lean_ctor_set(x_35, 0, x_38);
x_40 = x_35;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_38);
lean_ctor_set(x_53, 1, x_39);
x_40 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_51; 
x_41 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__3, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__3_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__3);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1___redArg(x_42, x_29, x_30, x_31, x_32);
lean_dec_ref(x_31);
x_44 = lean_ctor_get(x_43, 0);
x_51 = !lean_is_exclusive(x_43);
if (x_51 == 0)
{
x_45 = x_43;
x_46 = x_51;
goto block_50;
}
else
{
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_box(0);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_46 == 0)
{
x_47 = x_45;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_44);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
}
}
block_80:
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = l_Lean_Syntax_getId(x_1);
lean_inc(x_63);
x_64 = lean_erase_macro_scopes(x_63);
x_65 = l_Lean_Name_isAtomic(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_79; 
lean_dec(x_1);
x_66 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__5, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__5_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__5);
x_67 = l_Lean_MessageData_ofName(x_63);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__7, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__7_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__7);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1___redArg(x_70, x_59, x_60, x_61, x_62);
lean_dec_ref(x_61);
x_72 = lean_ctor_get(x_71, 0);
x_79 = !lean_is_exclusive(x_71);
if (x_79 == 0)
{
x_73 = x_71;
x_74 = x_79;
goto block_78;
}
else
{
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_box(0);
x_74 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_75; 
if (x_74 == 0)
{
x_75 = x_73;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_72);
x_75 = x_77;
goto block_76;
}
block_76:
{
return x_75;
}
}
}
else
{
x_27 = x_63;
x_28 = x_58;
x_29 = x_59;
x_30 = x_60;
x_31 = x_61;
x_32 = x_62;
goto block_57;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar_spec__0___redArg(x_2, x_3, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_1);
if (x_6 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec_ref(x_5);
x_7 = lean_box(0);
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
lean_inc(x_9);
lean_inc(x_8);
x_10 = l_Lean_Syntax_structEq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables_spec__0___redArg___closed__0));
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
x_4 = x_16;
x_5 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_array_get_size(x_4);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables_spec__0___redArg___closed__0));
x_10 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables_spec__0___redArg(x_6, x_4, x_5, x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
if (lean_obj_tag(x_11) == 0)
{
return x_8;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables_spec__0___redArg(x_1, x_2, x_3, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_104; 
x_10 = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__0, &l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__0);
x_11 = l_ReaderT_instMonad___redArg(x_10);
x_12 = lean_ctor_get(x_11, 0);
x_104 = !lean_is_exclusive(x_11);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_11, 1);
lean_dec(x_105);
x_13 = x_11;
x_14 = x_104;
goto block_103;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_101; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_ctor_get(x_12, 3);
x_18 = lean_ctor_get(x_12, 4);
x_101 = !lean_is_exclusive(x_12);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_12, 1);
lean_dec(x_102);
x_19 = x_12;
x_20 = x_101;
goto block_100;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__1));
x_22 = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__2));
lean_inc_ref(x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_18);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_17);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_28, 0, x_16);
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_26);
lean_ctor_set(x_19, 3, x_27);
lean_ctor_set(x_19, 2, x_28);
lean_ctor_set(x_19, 1, x_21);
lean_ctor_set(x_19, 0, x_25);
x_29 = x_19;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_99, 0, x_25);
lean_ctor_set(x_99, 1, x_21);
lean_ctor_set(x_99, 2, x_28);
lean_ctor_set(x_99, 3, x_27);
lean_ctor_set(x_99, 4, x_26);
x_29 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_30; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_29);
x_30 = x_13;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_29);
lean_ctor_set(x_97, 1, x_22);
x_30 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_94; 
x_31 = l_ReaderT_instMonad___redArg(x_30);
x_32 = lean_ctor_get(x_31, 0);
x_94 = !lean_is_exclusive(x_31);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_31, 1);
lean_dec(x_95);
x_33 = x_31;
x_34 = x_94;
goto block_93;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_91; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_ctor_get(x_32, 2);
x_37 = lean_ctor_get(x_32, 3);
x_38 = lean_ctor_get(x_32, 4);
x_91 = !lean_is_exclusive(x_32);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_32, 1);
lean_dec(x_92);
x_39 = x_32;
x_40 = x_91;
goto block_90;
}
else
{
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_32);
x_39 = lean_box(0);
x_40 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__3));
x_42 = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__4));
lean_inc_ref(x_35);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_43, 0, x_35);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_35);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_46, 0, x_38);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_47, 0, x_37);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_48, 0, x_36);
if (x_40 == 0)
{
lean_ctor_set(x_39, 4, x_46);
lean_ctor_set(x_39, 3, x_47);
lean_ctor_set(x_39, 2, x_48);
lean_ctor_set(x_39, 1, x_41);
lean_ctor_set(x_39, 0, x_45);
x_49 = x_39;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_89, 0, x_45);
lean_ctor_set(x_89, 1, x_41);
lean_ctor_set(x_89, 2, x_48);
lean_ctor_set(x_89, 3, x_47);
lean_ctor_set(x_89, 4, x_46);
x_49 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_50; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 1, x_42);
lean_ctor_set(x_33, 0, x_49);
x_50 = x_33;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_49);
lean_ctor_set(x_87, 1, x_42);
x_50 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_84; 
x_51 = l_ReaderT_instMonad___redArg(x_50);
x_52 = lean_ctor_get(x_51, 0);
x_84 = !lean_is_exclusive(x_51);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_51, 1);
lean_dec(x_85);
x_53 = x_51;
x_54 = x_84;
goto block_83;
}
else
{
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_box(0);
x_54 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_81; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_ctor_get(x_52, 2);
x_57 = lean_ctor_get(x_52, 3);
x_58 = lean_ctor_get(x_52, 4);
x_81 = !lean_is_exclusive(x_52);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_52, 1);
lean_dec(x_82);
x_59 = x_52;
x_60 = x_81;
goto block_80;
}
else
{
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_52);
x_59 = lean_box(0);
x_60 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_61 = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__5));
x_62 = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__6));
lean_inc_ref(x_55);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_63, 0, x_55);
x_64 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_64, 0, x_55);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_66, 0, x_58);
x_67 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_67, 0, x_57);
x_68 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_68, 0, x_56);
if (x_60 == 0)
{
lean_ctor_set(x_59, 4, x_66);
lean_ctor_set(x_59, 3, x_67);
lean_ctor_set(x_59, 2, x_68);
lean_ctor_set(x_59, 1, x_61);
lean_ctor_set(x_59, 0, x_65);
x_69 = x_59;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_65);
lean_ctor_set(x_79, 1, x_61);
lean_ctor_set(x_79, 2, x_68);
lean_ctor_set(x_79, 3, x_67);
lean_ctor_set(x_79, 4, x_66);
x_69 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_70; 
if (x_54 == 0)
{
lean_ctor_set(x_53, 1, x_62);
lean_ctor_set(x_53, 0, x_69);
x_70 = x_53;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_69);
lean_ctor_set(x_77, 1, x_62);
x_70 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = l_ReaderT_instMonad___redArg(x_70);
x_72 = l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default;
x_73 = l_instInhabitedOfMonad___redArg(x_71, x_72);
x_74 = lean_panic_fn(x_73, x_1);
x_75 = lean_apply_8(x_74, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_75;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__4(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__3);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_usize(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__4);
x_3 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__10));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__12));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__14));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__16));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__18));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = l_Lean_Name_isAnonymous(x_2);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
lean_inc_ref(x_6);
x_10 = l_Lean_Environment_setExporting(x_6, x_7);
lean_inc(x_2);
lean_inc_ref(x_10);
x_11 = l_Lean_Environment_contains(x_10, x_2, x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_10);
lean_dec_ref(x_6);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__2);
x_14 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__5);
x_15 = l_Lean_Options_empty;
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_15);
lean_inc(x_2);
x_17 = l_Lean_MessageData_ofConstName(x_2, x_7);
x_18 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Environment_getModuleIdxFor_x3f(x_6, x_2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_20 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__7);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__9);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_MessageData_note(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_62; 
x_27 = lean_ctor_get(x_19, 0);
x_62 = !lean_is_exclusive(x_19);
if (x_62 == 0)
{
x_28 = x_19;
x_29 = x_62;
goto block_61;
}
else
{
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_box(0);
x_29 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_box(0);
x_31 = l_Lean_Environment_header(x_6);
lean_dec_ref(x_6);
x_32 = l_Lean_EnvironmentHeader_moduleNames(x_31);
x_33 = lean_array_get(x_30, x_32, x_27);
lean_dec(x_27);
lean_dec_ref(x_32);
x_34 = l_Lean_isPrivateName(x_2);
lean_dec(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__11);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_18);
x_37 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__13);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_MessageData_ofName(x_33);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__15);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_MessageData_note(x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 0);
lean_ctor_set(x_28, 0, x_44);
x_45 = x_28;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_48 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__7);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_18);
x_50 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__17);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_MessageData_ofName(x_33);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___closed__19);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_MessageData_note(x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 0);
lean_ctor_set(x_28, 0, x_57);
x_58 = x_28;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_57);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
}
}
}
else
{
lean_object* x_63; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_1);
return x_63;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_21; 
x_11 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg(x_1, x_2, x_9);
x_12 = lean_ctor_get(x_11, 0);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
x_13 = x_11;
x_14 = x_21;
goto block_20;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_unknownIdentifierMessageTag;
x_16 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_16);
x_17 = x_13;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar_spec__0___redArg(x_1, x_13, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16___redArg___closed__1);
x_12 = 0;
lean_inc(x_2);
x_13 = l_Lean_MessageData_ofConstName(x_2, x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__4);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22___redArg(x_1, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 5);
lean_inc(x_10);
x_11 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16___redArg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_st_ref_get(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = 0;
lean_inc(x_1);
x_13 = l_Lean_Environment_find_x3f(x_11, x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
lean_dec_ref(x_7);
lean_dec(x_1);
x_15 = lean_ctor_get(x_13, 0);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
x_16 = x_13;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 0);
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__7___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_10(x_1, x_5, x_6, x_2, x_3, x_4, x_7, x_8, x_9, x_10, lean_box(0));
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__7___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__7___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__7___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__7___redArg___lam__0___boxed), 11, 4);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_5);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), x_1, x_13, x_3, x_4, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
x_15 = lean_ctor_get(x_14, 0);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
x_16 = x_14;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_3);
x_14 = lean_unbox(x_4);
x_15 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__7___redArg(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__5___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_4);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget_borrowed(x_3, x_2);
lean_inc_ref(x_4);
x_11 = l_Lean_Meta_getFVarLocalDecl___redArg(x_10, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = l_Lean_LocalDecl_userName(x_12);
x_16 = l_Lean_LocalDecl_binderInfo(x_12);
lean_dec(x_12);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_14, x_2, x_18);
x_2 = x_20;
x_3 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_23 = lean_ctor_get(x_11, 0);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
x_24 = x_11;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__5___redArg(x_8, x_9, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_array_size(x_1);
x_12 = 0;
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__5___redArg(x_11, x_12, x_1, x_6, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_name_eq(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__17_spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_nat_dec_lt(x_3, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_array_fget_borrowed(x_1, x_3);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_mod(x_3, x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_3, x_21);
lean_dec(x_3);
lean_inc(x_16);
x_23 = lean_array_push(x_4, x_16);
x_3 = x_22;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; 
lean_inc_ref(x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_16);
x_25 = lean_apply_9(x_2, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_3, x_27);
lean_dec(x_3);
x_29 = lean_array_push(x_4, x_26);
x_3 = x_28;
x_4 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_31 = lean_ctor_get(x_25, 0);
x_38 = !lean_is_exclusive(x_25);
if (x_38 == 0)
{
x_32 = x_25;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__17_spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__17_spec__23(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = ((lean_object*)(l_Array_mapSepElemsM___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__17___closed__0));
x_13 = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__17_spec__23(x_1, x_2, x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapSepElemsM___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19___closed__1));
lean_inc(x_11);
x_13 = l_Lean_Syntax_isOfKind(x_11, x_12);
if (x_13 == 0)
{
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_14; 
lean_inc(x_11);
x_14 = lean_array_push(x_4, x_11);
x_5 = x_14;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19___closed__1));
lean_inc(x_11);
x_13 = l_Lean_Syntax_isOfKind(x_11, x_12);
if (x_13 == 0)
{
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_14; 
lean_inc(x_11);
x_14 = lean_array_push(x_4, x_11);
x_5 = x_14;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19(x_1, x_7, x_3, x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_104; 
x_10 = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__0, &l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__0);
x_11 = l_ReaderT_instMonad___redArg(x_10);
x_12 = lean_ctor_get(x_11, 0);
x_104 = !lean_is_exclusive(x_11);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_11, 1);
lean_dec(x_105);
x_13 = x_11;
x_14 = x_104;
goto block_103;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_101; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_ctor_get(x_12, 3);
x_18 = lean_ctor_get(x_12, 4);
x_101 = !lean_is_exclusive(x_12);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_12, 1);
lean_dec(x_102);
x_19 = x_12;
x_20 = x_101;
goto block_100;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__1));
x_22 = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__2));
lean_inc_ref(x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_18);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_17);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_28, 0, x_16);
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_26);
lean_ctor_set(x_19, 3, x_27);
lean_ctor_set(x_19, 2, x_28);
lean_ctor_set(x_19, 1, x_21);
lean_ctor_set(x_19, 0, x_25);
x_29 = x_19;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_99, 0, x_25);
lean_ctor_set(x_99, 1, x_21);
lean_ctor_set(x_99, 2, x_28);
lean_ctor_set(x_99, 3, x_27);
lean_ctor_set(x_99, 4, x_26);
x_29 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_30; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_29);
x_30 = x_13;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_29);
lean_ctor_set(x_97, 1, x_22);
x_30 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_94; 
x_31 = l_ReaderT_instMonad___redArg(x_30);
x_32 = lean_ctor_get(x_31, 0);
x_94 = !lean_is_exclusive(x_31);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_31, 1);
lean_dec(x_95);
x_33 = x_31;
x_34 = x_94;
goto block_93;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_91; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_ctor_get(x_32, 2);
x_37 = lean_ctor_get(x_32, 3);
x_38 = lean_ctor_get(x_32, 4);
x_91 = !lean_is_exclusive(x_32);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_32, 1);
lean_dec(x_92);
x_39 = x_32;
x_40 = x_91;
goto block_90;
}
else
{
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_32);
x_39 = lean_box(0);
x_40 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__3));
x_42 = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__4));
lean_inc_ref(x_35);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_43, 0, x_35);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_35);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_46, 0, x_38);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_47, 0, x_37);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_48, 0, x_36);
if (x_40 == 0)
{
lean_ctor_set(x_39, 4, x_46);
lean_ctor_set(x_39, 3, x_47);
lean_ctor_set(x_39, 2, x_48);
lean_ctor_set(x_39, 1, x_41);
lean_ctor_set(x_39, 0, x_45);
x_49 = x_39;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_89, 0, x_45);
lean_ctor_set(x_89, 1, x_41);
lean_ctor_set(x_89, 2, x_48);
lean_ctor_set(x_89, 3, x_47);
lean_ctor_set(x_89, 4, x_46);
x_49 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_50; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 1, x_42);
lean_ctor_set(x_33, 0, x_49);
x_50 = x_33;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_49);
lean_ctor_set(x_87, 1, x_42);
x_50 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_84; 
x_51 = l_ReaderT_instMonad___redArg(x_50);
x_52 = lean_ctor_get(x_51, 0);
x_84 = !lean_is_exclusive(x_51);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_51, 1);
lean_dec(x_85);
x_53 = x_51;
x_54 = x_84;
goto block_83;
}
else
{
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_box(0);
x_54 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_81; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_ctor_get(x_52, 2);
x_57 = lean_ctor_get(x_52, 3);
x_58 = lean_ctor_get(x_52, 4);
x_81 = !lean_is_exclusive(x_52);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_52, 1);
lean_dec(x_82);
x_59 = x_52;
x_60 = x_81;
goto block_80;
}
else
{
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_52);
x_59 = lean_box(0);
x_60 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_61 = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__5));
x_62 = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__6));
lean_inc_ref(x_55);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_63, 0, x_55);
x_64 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_64, 0, x_55);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_66, 0, x_58);
x_67 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_67, 0, x_57);
x_68 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_68, 0, x_56);
if (x_60 == 0)
{
lean_ctor_set(x_59, 4, x_66);
lean_ctor_set(x_59, 3, x_67);
lean_ctor_set(x_59, 2, x_68);
lean_ctor_set(x_59, 1, x_61);
lean_ctor_set(x_59, 0, x_65);
x_69 = x_59;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_65);
lean_ctor_set(x_79, 1, x_61);
lean_ctor_set(x_79, 2, x_68);
lean_ctor_set(x_79, 3, x_67);
lean_ctor_set(x_79, 4, x_66);
x_69 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_70; 
if (x_54 == 0)
{
lean_ctor_set(x_53, 1, x_62);
lean_ctor_set(x_53, 0, x_69);
x_70 = x_53;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_69);
lean_ctor_set(x_77, 1, x_62);
x_70 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = l_ReaderT_instMonad___redArg(x_70);
x_72 = lean_box(0);
x_73 = l_instInhabitedOfMonad___redArg(x_71, x_72);
x_74 = lean_panic_fn(x_73, x_1);
x_75 = lean_apply_8(x_74, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_75;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_104; 
x_10 = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__0, &l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__0);
x_11 = l_ReaderT_instMonad___redArg(x_10);
x_12 = lean_ctor_get(x_11, 0);
x_104 = !lean_is_exclusive(x_11);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_11, 1);
lean_dec(x_105);
x_13 = x_11;
x_14 = x_104;
goto block_103;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_101; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_ctor_get(x_12, 3);
x_18 = lean_ctor_get(x_12, 4);
x_101 = !lean_is_exclusive(x_12);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_12, 1);
lean_dec(x_102);
x_19 = x_12;
x_20 = x_101;
goto block_100;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__1));
x_22 = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__2));
lean_inc_ref(x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_18);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_17);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_28, 0, x_16);
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_26);
lean_ctor_set(x_19, 3, x_27);
lean_ctor_set(x_19, 2, x_28);
lean_ctor_set(x_19, 1, x_21);
lean_ctor_set(x_19, 0, x_25);
x_29 = x_19;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_99, 0, x_25);
lean_ctor_set(x_99, 1, x_21);
lean_ctor_set(x_99, 2, x_28);
lean_ctor_set(x_99, 3, x_27);
lean_ctor_set(x_99, 4, x_26);
x_29 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_30; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_29);
x_30 = x_13;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_29);
lean_ctor_set(x_97, 1, x_22);
x_30 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_94; 
x_31 = l_ReaderT_instMonad___redArg(x_30);
x_32 = lean_ctor_get(x_31, 0);
x_94 = !lean_is_exclusive(x_31);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_31, 1);
lean_dec(x_95);
x_33 = x_31;
x_34 = x_94;
goto block_93;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_91; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_ctor_get(x_32, 2);
x_37 = lean_ctor_get(x_32, 3);
x_38 = lean_ctor_get(x_32, 4);
x_91 = !lean_is_exclusive(x_32);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_32, 1);
lean_dec(x_92);
x_39 = x_32;
x_40 = x_91;
goto block_90;
}
else
{
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_32);
x_39 = lean_box(0);
x_40 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__3));
x_42 = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__4));
lean_inc_ref(x_35);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_43, 0, x_35);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_35);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_46, 0, x_38);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_47, 0, x_37);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_48, 0, x_36);
if (x_40 == 0)
{
lean_ctor_set(x_39, 4, x_46);
lean_ctor_set(x_39, 3, x_47);
lean_ctor_set(x_39, 2, x_48);
lean_ctor_set(x_39, 1, x_41);
lean_ctor_set(x_39, 0, x_45);
x_49 = x_39;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_89, 0, x_45);
lean_ctor_set(x_89, 1, x_41);
lean_ctor_set(x_89, 2, x_48);
lean_ctor_set(x_89, 3, x_47);
lean_ctor_set(x_89, 4, x_46);
x_49 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_50; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 1, x_42);
lean_ctor_set(x_33, 0, x_49);
x_50 = x_33;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_49);
lean_ctor_set(x_87, 1, x_42);
x_50 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_84; 
x_51 = l_ReaderT_instMonad___redArg(x_50);
x_52 = lean_ctor_get(x_51, 0);
x_84 = !lean_is_exclusive(x_51);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_51, 1);
lean_dec(x_85);
x_53 = x_51;
x_54 = x_84;
goto block_83;
}
else
{
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_box(0);
x_54 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_81; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_ctor_get(x_52, 2);
x_57 = lean_ctor_get(x_52, 3);
x_58 = lean_ctor_get(x_52, 4);
x_81 = !lean_is_exclusive(x_52);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_52, 1);
lean_dec(x_82);
x_59 = x_52;
x_60 = x_81;
goto block_80;
}
else
{
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_52);
x_59 = lean_box(0);
x_60 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_61 = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__5));
x_62 = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11___closed__6));
lean_inc_ref(x_55);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_63, 0, x_55);
x_64 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_64, 0, x_55);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_66, 0, x_58);
x_67 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_67, 0, x_57);
x_68 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_68, 0, x_56);
if (x_60 == 0)
{
lean_ctor_set(x_59, 4, x_66);
lean_ctor_set(x_59, 3, x_67);
lean_ctor_set(x_59, 2, x_68);
lean_ctor_set(x_59, 1, x_61);
lean_ctor_set(x_59, 0, x_65);
x_69 = x_59;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_65);
lean_ctor_set(x_79, 1, x_61);
lean_ctor_set(x_79, 2, x_68);
lean_ctor_set(x_79, 3, x_67);
lean_ctor_set(x_79, 4, x_66);
x_69 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_70; 
if (x_54 == 0)
{
lean_ctor_set(x_53, 1, x_62);
lean_ctor_set(x_53, 0, x_69);
x_70 = x_53;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_69);
lean_ctor_set(x_77, 1, x_62);
x_70 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = l_ReaderT_instMonad___redArg(x_70);
x_72 = lean_box(0);
x_73 = l_instInhabitedOfMonad___redArg(x_71, x_72);
x_74 = lean_panic_fn(x_73, x_1);
x_75 = lean_apply_8(x_74, x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_75;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__16_spec__21(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_uget_borrowed(x_1, x_2);
x_6 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19___closed__1));
lean_inc(x_5);
x_7 = l_Lean_Syntax_isOfKind(x_5, x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
else
{
return x_7;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__16_spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__16_spec__21(x_1, x_4, x_5);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__16(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_uget_borrowed(x_1, x_2);
x_6 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19___closed__1));
lean_inc(x_5);
x_7 = l_Lean_Syntax_isOfKind(x_5, x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; uint8_t x_10; 
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__16_spec__21(x_1, x_9, x_3);
return x_10;
}
else
{
return x_7;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__16(x_1, x_4, x_5);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__8(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_25; uint8_t x_36; 
x_15 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__1));
x_16 = lean_array_uget(x_4, x_3);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_4, x_3, x_17);
lean_inc(x_16);
x_36 = l_Lean_Syntax_isOfKind(x_16, x_15);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_16);
x_37 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg(x_8, x_9, x_10, x_11);
x_25 = x_37;
goto block_35;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = l_Lean_Syntax_getArg(x_16, x_17);
x_39 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__3));
lean_inc(x_38);
x_40 = l_Lean_Syntax_isOfKind(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_38);
lean_dec(x_16);
x_41 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg(x_8, x_9, x_10, x_11);
x_25 = x_41;
goto block_35;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_unsigned_to_nat(3u);
x_44 = l_Lean_Syntax_getArg(x_16, x_42);
lean_dec(x_16);
lean_inc(x_44);
x_45 = l_Lean_Syntax_matchesNull(x_44, x_43);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_44);
lean_dec(x_38);
x_46 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg(x_8, x_9, x_10, x_11);
x_25 = x_46;
goto block_35;
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = l_Lean_Syntax_getArg(x_44, x_17);
x_48 = l_Lean_Syntax_matchesNull(x_47, x_17);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_44);
lean_dec(x_38);
x_49 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg(x_8, x_9, x_10, x_11);
x_25 = x_49;
goto block_35;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = l_Lean_Syntax_getArg(x_44, x_42);
x_51 = l_Lean_Syntax_matchesNull(x_50, x_17);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_44);
lean_dec(x_38);
x_52 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg(x_8, x_9, x_10, x_11);
x_25 = x_52;
goto block_35;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_unsigned_to_nat(2u);
x_54 = l_Lean_Syntax_getArg(x_44, x_53);
lean_dec(x_44);
x_55 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__5));
lean_inc(x_54);
x_56 = l_Lean_Syntax_isOfKind(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_38);
x_57 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg(x_8, x_9, x_10, x_11);
x_25 = x_57;
goto block_35;
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = l_Lean_Syntax_getArg(x_54, x_42);
x_59 = l_Lean_Syntax_matchesNull(x_58, x_17);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_54);
lean_dec(x_38);
x_60 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg(x_8, x_9, x_10, x_11);
x_25 = x_60;
goto block_35;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_Syntax_getArg(x_54, x_53);
lean_dec(x_54);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_62 = l_Lean_Elab_Term_CollectPatternVars_collect(x_61, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = lean_ctor_get(x_10, 5);
x_65 = l_Lean_SourceInfo_fromRef(x_64, x_1);
x_66 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__7));
x_67 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__8);
lean_inc(x_65);
x_68 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
lean_ctor_set(x_68, 2, x_67);
x_69 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__4));
lean_inc(x_65);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_69);
lean_inc_ref(x_68);
lean_inc(x_65);
x_71 = l_Lean_Syntax_node3(x_65, x_55, x_70, x_68, x_63);
lean_inc_ref(x_68);
lean_inc(x_65);
x_72 = l_Lean_Syntax_node3(x_65, x_66, x_68, x_68, x_71);
x_73 = l_Lean_Syntax_node2(x_65, x_15, x_38, x_72);
x_19 = x_73;
goto block_24;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_81; 
lean_dec(x_38);
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_74 = lean_ctor_get(x_62, 0);
x_81 = !lean_is_exclusive(x_62);
if (x_81 == 0)
{
x_75 = x_62;
x_76 = x_81;
goto block_80;
}
else
{
lean_inc(x_74);
lean_dec(x_62);
x_75 = lean_box(0);
x_76 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_77; 
if (x_76 == 0)
{
x_77 = x_75;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_74);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
}
}
}
}
}
}
}
}
block_24:
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_22 = lean_array_uset(x_18, x_3, x_19);
x_3 = x_21;
x_4 = x_22;
goto _start;
}
block_35:
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_19 = x_26;
goto block_24;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_27 = lean_ctor_get(x_25, 0);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
x_28 = x_25;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__38(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__37));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__14___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__14___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__14___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_55; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_55 = !lean_is_exclusive(x_3);
if (x_55 == 0)
{
x_16 = x_3;
x_17 = x_55;
goto block_54;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_16 = lean_box(0);
x_17 = x_55;
goto block_54;
}
block_54:
{
uint8_t x_18; 
x_18 = lean_nat_dec_lt(x_14, x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_del_object(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc_ref(x_1);
x_20 = lean_st_ref_set(x_5, x_1);
x_21 = lean_array_fget_borrowed(x_13, x_14);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_21);
x_22 = l_Lean_Elab_Term_CollectPatternVars_collect(x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_st_ref_get(x_5);
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_14, x_26);
lean_dec(x_14);
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_27);
x_28 = x_16;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_13);
lean_ctor_set(x_45, 1, x_27);
lean_ctor_set(x_45, 2, x_15);
x_28 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_array_push(x_4, x_23);
x_30 = lean_array_get_size(x_25);
x_31 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables(x_30, x_2, x_24);
lean_dec(x_24);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__14___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__14___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__14___redArg___closed__1);
x_33 = l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1___redArg(x_32, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_33) == 0)
{
lean_dec_ref(x_33);
x_3 = x_28;
x_4 = x_29;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_35 = lean_ctor_get(x_33, 0);
x_42 = !lean_is_exclusive(x_33);
if (x_42 == 0)
{
x_36 = x_33;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
x_3 = x_28;
x_4 = x_29;
goto _start;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_53; 
lean_del_object(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_46 = lean_ctor_get(x_22, 0);
x_53 = !lean_is_exclusive(x_22);
if (x_53 == 0)
{
x_47 = x_22;
x_48 = x_53;
goto block_52;
}
else
{
lean_inc(x_46);
lean_dec(x_22);
x_47 = lean_box(0);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_48 == 0)
{
x_49 = x_47;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_46);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__44(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__43));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__51(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__50));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_CollectPatternVars_collect(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__2));
x_2 = lean_unsigned_to_nat(15u);
x_3 = lean_unsigned_to_nat(324u);
x_4 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__3___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_2, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_14 = lean_array_uget_borrowed(x_3, x_2);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 2);
lean_inc_ref(x_16);
x_17 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_3, x_2, x_18);
if (lean_obj_tag(x_16) == 0)
{
if (x_17 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_45 = lean_ctor_get(x_16, 0);
lean_inc(x_45);
lean_dec_ref(x_16);
x_46 = lean_ctor_get(x_9, 0);
x_47 = lean_ctor_get(x_9, 1);
x_48 = lean_ctor_get(x_9, 2);
x_49 = lean_ctor_get(x_9, 3);
x_50 = lean_ctor_get(x_9, 4);
x_51 = lean_ctor_get(x_9, 5);
x_52 = lean_ctor_get(x_9, 6);
x_53 = lean_ctor_get(x_9, 7);
x_54 = lean_ctor_get(x_9, 8);
x_55 = lean_ctor_get(x_9, 9);
x_56 = lean_ctor_get(x_9, 10);
x_57 = lean_ctor_get(x_9, 11);
x_58 = lean_ctor_get_uint8(x_9, sizeof(void*)*14);
x_59 = lean_ctor_get(x_9, 12);
x_60 = lean_ctor_get_uint8(x_9, sizeof(void*)*14 + 1);
x_61 = lean_ctor_get(x_9, 13);
x_62 = l_Lean_replaceRef(x_15, x_51);
lean_inc_ref(x_61);
lean_inc(x_59);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_62);
lean_inc(x_50);
lean_inc(x_49);
lean_inc_ref(x_48);
lean_inc_ref(x_47);
lean_inc_ref(x_46);
x_63 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_63, 0, x_46);
lean_ctor_set(x_63, 1, x_47);
lean_ctor_set(x_63, 2, x_48);
lean_ctor_set(x_63, 3, x_49);
lean_ctor_set(x_63, 4, x_50);
lean_ctor_set(x_63, 5, x_62);
lean_ctor_set(x_63, 6, x_52);
lean_ctor_set(x_63, 7, x_53);
lean_ctor_set(x_63, 8, x_54);
lean_ctor_set(x_63, 9, x_55);
lean_ctor_set(x_63, 10, x_56);
lean_ctor_set(x_63, 11, x_57);
lean_ctor_set(x_63, 12, x_59);
lean_ctor_set(x_63, 13, x_61);
lean_ctor_set_uint8(x_63, sizeof(void*)*14, x_58);
lean_ctor_set_uint8(x_63, sizeof(void*)*14 + 1, x_60);
lean_inc(x_10);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_64 = l_Lean_Elab_Term_CollectPatternVars_collect(x_45, x_4, x_5, x_6, x_7, x_8, x_63, x_10);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = l_Lean_SourceInfo_fromRef(x_62, x_17);
lean_dec(x_62);
x_67 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__2));
x_68 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__3));
lean_inc(x_66);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_unsigned_to_nat(1u);
x_71 = l_Lean_Syntax_getArg(x_15, x_70);
lean_dec(x_15);
x_72 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__4));
lean_inc(x_66);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_66);
lean_ctor_set(x_73, 1, x_72);
x_74 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__5));
lean_inc(x_66);
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_66);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_Syntax_node5(x_66, x_67, x_69, x_71, x_73, x_65, x_75);
x_20 = x_76;
goto block_25;
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_84; 
lean_dec(x_62);
lean_dec_ref(x_19);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_77 = lean_ctor_get(x_64, 0);
x_84 = !lean_is_exclusive(x_64);
if (x_84 == 0)
{
x_78 = x_64;
x_79 = x_84;
goto block_83;
}
else
{
lean_inc(x_77);
lean_dec(x_64);
x_78 = lean_box(0);
x_79 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_80; 
if (x_79 == 0)
{
x_80 = x_78;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_77);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
}
else
{
lean_dec_ref(x_16);
lean_dec(x_15);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
goto block_44;
}
}
else
{
lean_dec_ref(x_16);
lean_dec(x_15);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
goto block_44;
}
block_25:
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_array_uset(x_19, x_2, x_20);
x_2 = x_22;
x_3 = x_23;
goto _start;
}
block_44:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__0);
x_34 = l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__0(x_33, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_20 = x_35;
goto block_25;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_43; 
lean_dec_ref(x_19);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_36 = lean_ctor_get(x_34, 0);
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
x_37 = x_34;
x_38 = x_43;
goto block_42;
}
else
{
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_box(0);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_38 == 0)
{
x_39 = x_37;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_36);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__3___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__2));
x_2 = lean_unsigned_to_nat(74u);
x_3 = lean_unsigned_to_nat(325u);
x_4 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__3___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_2, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_uget(x_3, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec_ref(x_14);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_24 = l_Lean_Elab_Term_CollectPatternVars_collect(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_17 = x_25;
goto block_22;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec_ref(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_26 = lean_ctor_get(x_24, 0);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
x_27 = x_24;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_14);
x_34 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__3___closed__1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_35 = l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__1(x_34, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_17 = x_36;
goto block_22;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec_ref(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_37 = lean_ctor_get(x_35, 0);
x_44 = !lean_is_exclusive(x_35);
if (x_44 == 0)
{
x_38 = x_35;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
block_22:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_16, x_2, x_17);
x_2 = x_19;
x_3 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
lean_inc_ref(x_7);
x_10 = l_Lean_Elab_Term_expandApp(x_1, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
lean_inc(x_14);
x_18 = l_Lean_Syntax_getKind(x_14);
x_19 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__1));
x_20 = lean_name_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; 
x_21 = lean_unbox(x_17);
lean_dec(x_17);
x_22 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore(x_14, x_15, x_16, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_22;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = lean_array_size(x_15);
x_24 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_25 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2(x_23, x_24, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; size_t x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_array_size(x_16);
x_28 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__3(x_27, x_24, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_51; 
x_29 = lean_ctor_get(x_28, 0);
x_51 = !lean_is_exclusive(x_28);
if (x_51 == 0)
{
x_30 = x_28;
x_31 = x_51;
goto block_50;
}
else
{
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_32; uint8_t x_39; 
x_39 = lean_unbox(x_17);
lean_dec(x_17);
if (x_39 == 0)
{
x_32 = x_29;
goto block_38;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__3));
x_41 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__4));
x_42 = 0;
x_43 = l_Lean_mkAtomFrom(x_1, x_41, x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_mk_empty_array_with_capacity(x_44);
x_46 = lean_array_push(x_45, x_43);
x_47 = lean_box(2);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_40);
lean_ctor_set(x_48, 2, x_46);
x_49 = lean_array_push(x_29, x_48);
x_32 = x_49;
goto block_38;
}
block_38:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Array_append___redArg(x_26, x_32);
lean_dec_ref(x_32);
x_34 = l_Lean_Syntax_mkApp(x_14, x_33);
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_34);
x_35 = x_30;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_59; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_14);
x_52 = lean_ctor_get(x_28, 0);
x_59 = !lean_is_exclusive(x_28);
if (x_59 == 0)
{
x_53 = x_28;
x_54 = x_59;
goto block_58;
}
else
{
lean_inc(x_52);
lean_dec(x_28);
x_53 = lean_box(0);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_54 == 0)
{
x_55 = x_53;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_52);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_67; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_60 = lean_ctor_get(x_25, 0);
x_67 = !lean_is_exclusive(x_25);
if (x_67 == 0)
{
x_61 = x_25;
x_62 = x_67;
goto block_66;
}
else
{
lean_inc(x_60);
lean_dec(x_25);
x_61 = lean_box(0);
x_62 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_63; 
if (x_62 == 0)
{
x_63 = x_61;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_60);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_75; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_68 = lean_ctor_get(x_10, 0);
x_75 = !lean_is_exclusive(x_10);
if (x_75 == 0)
{
x_69 = x_10;
x_70 = x_75;
goto block_74;
}
else
{
lean_inc(x_68);
lean_dec(x_10);
x_69 = lean_box(0);
x_70 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_71; 
if (x_70 == 0)
{
x_71 = x_69;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_68);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processId___closed__0));
x_11 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_1);
x_12 = l_Lean_Elab_Term_resolveId_x3f(x_1, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_35; 
x_15 = lean_ctor_get(x_13, 0);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
x_16 = x_13;
x_17 = x_35;
goto block_34;
}
else
{
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = x_35;
goto block_34;
}
block_34:
{
if (lean_obj_tag(x_15) == 4)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = lean_st_ref_get(x_8);
x_20 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_20);
lean_dec(x_19);
lean_inc(x_18);
x_21 = l_Lean_Environment_find_x3f(x_20, x_18, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec(x_18);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_1);
x_22 = x_16;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_1);
x_22 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_23; 
x_23 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_23;
}
}
else
{
lean_object* x_26; 
lean_del_object(x_16);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec_ref(x_21);
if (lean_obj_tag(x_26) == 6)
{
lean_object* x_27; 
lean_dec_ref(x_26);
lean_dec(x_18);
x_27 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_26);
x_28 = lean_st_ref_get(x_8);
x_29 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_29);
lean_dec(x_28);
x_30 = lean_has_match_pattern_attribute(x_29, x_18);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_32;
}
}
}
}
else
{
lean_object* x_33; 
lean_del_object(x_16);
lean_dec(x_15);
x_33 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_33;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_43; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_ctor_get(x_12, 0);
x_43 = !lean_is_exclusive(x_12);
if (x_43 == 0)
{
x_37 = x_12;
x_38 = x_43;
goto block_42;
}
else
{
lean_inc(x_36);
lean_dec(x_12);
x_37 = lean_box(0);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_38 == 0)
{
x_39 = x_37;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_36);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
if (x_1 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__1));
x_39 = lean_name_eq(x_2, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__3));
x_41 = lean_name_eq(x_2, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__1));
x_43 = lean_name_eq(x_2, x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___closed__1));
x_45 = lean_name_eq(x_2, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__5));
x_47 = lean_name_eq(x_2, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__7));
x_49 = lean_name_eq(x_2, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__9));
x_51 = lean_name_eq(x_2, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__4));
x_53 = lean_name_eq(x_2, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__11));
x_55 = lean_name_eq(x_2, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__13));
x_57 = lean_name_eq(x_2, x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__15));
x_59 = lean_name_eq(x_2, x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__17));
x_61 = lean_name_eq(x_2, x_60);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__19));
x_63 = lean_name_eq(x_2, x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__21));
x_65 = lean_name_eq(x_2, x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__23));
x_67 = lean_name_eq(x_2, x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__25));
x_69 = lean_name_eq(x_2, x_68);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__27));
x_71 = lean_name_eq(x_2, x_70);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__29));
x_73 = lean_name_eq(x_2, x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__31));
x_75 = lean_name_eq(x_2, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_92; 
x_76 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15_spec__19___closed__1));
lean_inc(x_3);
x_92 = l_Lean_Syntax_isOfKind(x_3, x_76);
if (x_92 == 0)
{
lean_object* x_93; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_93 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg(x_4, x_5, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_259; uint8_t x_260; 
x_94 = lean_unsigned_to_nat(0u);
x_209 = lean_unsigned_to_nat(1u);
x_259 = l_Lean_Syntax_getArg(x_3, x_209);
x_260 = l_Lean_Syntax_isNone(x_259);
if (x_260 == 0)
{
lean_object* x_261; uint8_t x_262; 
x_261 = lean_unsigned_to_nat(2u);
lean_inc(x_259);
x_262 = l_Lean_Syntax_matchesNull(x_259, x_261);
if (x_262 == 0)
{
lean_object* x_263; 
lean_dec(x_259);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_263 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg(x_4, x_5, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_263;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = l_Lean_Syntax_getArg(x_259, x_94);
lean_dec(x_259);
x_265 = l_Lean_Syntax_getArgs(x_264);
lean_dec(x_264);
x_266 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_266, 0, x_265);
x_232 = x_266;
x_233 = x_7;
x_234 = x_8;
x_235 = x_9;
x_236 = x_4;
x_237 = x_5;
x_238 = x_10;
x_239 = x_11;
goto block_258;
}
}
else
{
lean_object* x_267; 
lean_dec(x_259);
x_267 = lean_box(0);
x_232 = x_267;
x_233 = x_7;
x_234 = x_8;
x_235 = x_9;
x_236 = x_4;
x_237 = x_5;
x_238 = x_10;
x_239 = x_11;
goto block_258;
}
block_112:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_inc_ref(x_100);
x_104 = l_Array_append___redArg(x_100, x_103);
lean_dec_ref(x_103);
lean_inc(x_98);
lean_inc(x_96);
x_105 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_105, 0, x_96);
lean_ctor_set(x_105, 1, x_98);
lean_ctor_set(x_105, 2, x_104);
lean_inc(x_96);
x_106 = l_Lean_Syntax_node1(x_96, x_99, x_105);
if (lean_obj_tag(x_97) == 1)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_97, 0);
lean_inc(x_107);
lean_dec_ref(x_97);
x_108 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__33));
lean_inc(x_96);
x_109 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_109, 0, x_96);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Array_mkArray2___redArg(x_109, x_107);
x_77 = x_95;
x_78 = x_96;
x_79 = x_106;
x_80 = x_98;
x_81 = x_100;
x_82 = x_101;
x_83 = x_102;
x_84 = x_110;
goto block_91;
}
else
{
lean_object* x_111; 
lean_dec(x_97);
x_111 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_instInhabitedState_default___closed__0));
x_77 = x_95;
x_78 = x_96;
x_79 = x_106;
x_80 = x_98;
x_81 = x_100;
x_82 = x_101;
x_83 = x_102;
x_84 = x_111;
goto block_91;
}
}
block_136:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_inc_ref(x_120);
x_124 = l_Array_append___redArg(x_120, x_123);
lean_dec_ref(x_123);
lean_inc(x_118);
lean_inc(x_114);
x_125 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_125, 0, x_114);
lean_ctor_set(x_125, 1, x_118);
lean_ctor_set(x_125, 2, x_124);
x_126 = l_Lean_Syntax_SepArray_ofElems(x_115, x_122);
lean_dec_ref(x_122);
lean_inc_ref(x_120);
x_127 = l_Array_append___redArg(x_120, x_126);
lean_dec_ref(x_126);
lean_inc(x_118);
lean_inc(x_114);
x_128 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_128, 0, x_114);
lean_ctor_set(x_128, 1, x_118);
lean_ctor_set(x_128, 2, x_127);
lean_inc(x_114);
x_129 = l_Lean_Syntax_node1(x_114, x_116, x_128);
if (lean_obj_tag(x_121) == 1)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_ctor_get(x_121, 0);
lean_inc(x_130);
lean_dec_ref(x_121);
x_131 = l_Lean_SourceInfo_fromRef(x_130, x_6);
lean_dec(x_130);
x_132 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__4));
x_133 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Array_mkArray1___redArg(x_133);
x_95 = x_113;
x_96 = x_114;
x_97 = x_117;
x_98 = x_118;
x_99 = x_119;
x_100 = x_120;
x_101 = x_125;
x_102 = x_129;
x_103 = x_134;
goto block_112;
}
else
{
lean_object* x_135; 
lean_dec(x_121);
x_135 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_instInhabitedState_default___closed__0));
x_95 = x_113;
x_96 = x_114;
x_97 = x_117;
x_98 = x_118;
x_99 = x_119;
x_100 = x_120;
x_101 = x_125;
x_102 = x_129;
x_103 = x_135;
goto block_112;
}
}
block_177:
{
lean_object* x_151; size_t x_152; size_t x_153; lean_object* x_154; 
x_151 = l_Lean_Syntax_TSepArray_getElems___redArg(x_143);
lean_dec_ref(x_143);
x_152 = lean_array_size(x_151);
x_153 = 0;
lean_inc_ref(x_149);
x_154 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13(x_75, x_152, x_153, x_151, x_144, x_145, x_146, x_147, x_148, x_149, x_150);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
lean_dec_ref(x_154);
x_156 = lean_ctor_get(x_149, 5);
lean_inc(x_156);
lean_dec_ref(x_149);
x_157 = l_Lean_SourceInfo_fromRef(x_156, x_75);
lean_dec(x_156);
x_158 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__34));
lean_inc(x_157);
x_159 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__7));
x_161 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__8, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__8);
if (lean_obj_tag(x_141) == 1)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_162 = lean_ctor_get(x_141, 0);
lean_inc(x_162);
lean_dec_ref(x_141);
x_163 = l_Array_append___redArg(x_161, x_162);
lean_dec(x_162);
lean_inc(x_157);
x_164 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_164, 0, x_157);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set(x_164, 2, x_163);
x_165 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__35));
lean_inc(x_157);
x_166 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_166, 0, x_157);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Array_mkArray2___redArg(x_164, x_166);
x_113 = x_159;
x_114 = x_157;
x_115 = x_137;
x_116 = x_138;
x_117 = x_139;
x_118 = x_160;
x_119 = x_140;
x_120 = x_161;
x_121 = x_142;
x_122 = x_155;
x_123 = x_167;
goto block_136;
}
else
{
lean_object* x_168; 
lean_dec(x_141);
x_168 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_instInhabitedState_default___closed__0));
x_113 = x_159;
x_114 = x_157;
x_115 = x_137;
x_116 = x_138;
x_117 = x_139;
x_118 = x_160;
x_119 = x_140;
x_120 = x_161;
x_121 = x_142;
x_122 = x_155;
x_123 = x_168;
goto block_136;
}
}
else
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; uint8_t x_176; 
lean_dec_ref(x_149);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec_ref(x_137);
x_169 = lean_ctor_get(x_154, 0);
x_176 = !lean_is_exclusive(x_154);
if (x_176 == 0)
{
x_170 = x_154;
x_171 = x_176;
goto block_175;
}
else
{
lean_inc(x_169);
lean_dec(x_154);
x_170 = lean_box(0);
x_171 = x_176;
goto block_175;
}
block_175:
{
lean_object* x_172; 
if (x_171 == 0)
{
x_172 = x_170;
goto block_173;
}
else
{
lean_object* x_174; 
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_169);
x_172 = x_174;
goto block_173;
}
block_173:
{
return x_172;
}
}
}
}
block_208:
{
lean_object* x_191; lean_object* x_192; 
x_191 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__36));
x_192 = l_Lean_Syntax_getArgs(x_182);
lean_dec(x_182);
if (lean_obj_tag(x_180) == 1)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_193 = lean_ctor_get(x_180, 0);
x_194 = l_Lean_Syntax_TSepArray_getElems___redArg(x_193);
x_195 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__7));
x_196 = lean_box(2);
x_197 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_195);
lean_ctor_set(x_197, 2, x_194);
x_198 = lean_obj_once(&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__38, &l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__38_once, _init_l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__38);
lean_inc_ref(x_189);
x_199 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar_spec__0___redArg(x_197, x_198, x_187, x_188, x_189, x_190);
lean_dec_ref(x_197);
if (lean_obj_tag(x_199) == 0)
{
lean_dec_ref(x_199);
x_137 = x_191;
x_138 = x_178;
x_139 = x_183;
x_140 = x_179;
x_141 = x_180;
x_142 = x_181;
x_143 = x_192;
x_144 = x_184;
x_145 = x_185;
x_146 = x_186;
x_147 = x_187;
x_148 = x_188;
x_149 = x_189;
x_150 = x_190;
goto block_177;
}
else
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; uint8_t x_207; 
lean_dec_ref(x_180);
lean_dec_ref(x_192);
lean_dec(x_190);
lean_dec_ref(x_189);
lean_dec(x_188);
lean_dec_ref(x_187);
lean_dec(x_186);
lean_dec_ref(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_181);
lean_dec(x_179);
lean_dec(x_178);
x_200 = lean_ctor_get(x_199, 0);
x_207 = !lean_is_exclusive(x_199);
if (x_207 == 0)
{
x_201 = x_199;
x_202 = x_207;
goto block_206;
}
else
{
lean_inc(x_200);
lean_dec(x_199);
x_201 = lean_box(0);
x_202 = x_207;
goto block_206;
}
block_206:
{
lean_object* x_203; 
if (x_202 == 0)
{
x_203 = x_201;
goto block_204;
}
else
{
lean_object* x_205; 
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_200);
x_203 = x_205;
goto block_204;
}
block_204:
{
return x_203;
}
}
}
}
else
{
x_137 = x_191;
x_138 = x_178;
x_139 = x_183;
x_140 = x_179;
x_141 = x_180;
x_142 = x_181;
x_143 = x_192;
x_144 = x_184;
x_145 = x_185;
x_146 = x_186;
x_147 = x_187;
x_148 = x_188;
x_149 = x_189;
x_150 = x_190;
goto block_177;
}
}
block_231:
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_223 = lean_unsigned_to_nat(4u);
x_224 = l_Lean_Syntax_getArg(x_3, x_223);
lean_dec(x_3);
x_225 = l_Lean_Syntax_isNone(x_224);
if (x_225 == 0)
{
uint8_t x_226; 
lean_inc(x_224);
x_226 = l_Lean_Syntax_matchesNull(x_224, x_213);
if (x_226 == 0)
{
lean_object* x_227; 
lean_dec(x_224);
lean_dec(x_218);
lean_dec_ref(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_210);
x_227 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg(x_219, x_220, x_221, x_222);
lean_dec(x_222);
lean_dec_ref(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; 
x_228 = l_Lean_Syntax_getArg(x_224, x_209);
lean_dec(x_224);
x_229 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_229, 0, x_228);
x_178 = x_210;
x_179 = x_211;
x_180 = x_212;
x_181 = x_215;
x_182 = x_214;
x_183 = x_229;
x_184 = x_216;
x_185 = x_217;
x_186 = x_218;
x_187 = x_219;
x_188 = x_220;
x_189 = x_221;
x_190 = x_222;
goto block_208;
}
}
else
{
lean_object* x_230; 
lean_dec(x_224);
x_230 = lean_box(0);
x_178 = x_210;
x_179 = x_211;
x_180 = x_212;
x_181 = x_215;
x_182 = x_214;
x_183 = x_230;
x_184 = x_216;
x_185 = x_217;
x_186 = x_218;
x_187 = x_219;
x_188 = x_220;
x_189 = x_221;
x_190 = x_222;
goto block_208;
}
}
block_258:
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_240 = lean_unsigned_to_nat(2u);
x_241 = l_Lean_Syntax_getArg(x_3, x_240);
x_242 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__40));
lean_inc(x_241);
x_243 = l_Lean_Syntax_isOfKind(x_241, x_242);
if (x_243 == 0)
{
lean_object* x_244; 
lean_dec(x_241);
lean_dec(x_235);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_3);
x_244 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg(x_236, x_237, x_238, x_239);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_245 = lean_unsigned_to_nat(3u);
x_246 = l_Lean_Syntax_getArg(x_3, x_245);
x_247 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__42));
lean_inc(x_246);
x_248 = l_Lean_Syntax_isOfKind(x_246, x_247);
if (x_248 == 0)
{
lean_object* x_249; 
lean_dec(x_246);
lean_dec(x_241);
lean_dec(x_235);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_3);
x_249 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg(x_236, x_237, x_238, x_239);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_250 = l_Lean_Syntax_getArg(x_241, x_94);
lean_dec(x_241);
x_251 = l_Lean_Syntax_getArg(x_246, x_94);
lean_dec(x_246);
x_252 = l_Lean_Syntax_isNone(x_251);
if (x_252 == 0)
{
uint8_t x_253; 
lean_inc(x_251);
x_253 = l_Lean_Syntax_matchesNull(x_251, x_209);
if (x_253 == 0)
{
lean_object* x_254; 
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_235);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_3);
x_254 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___redArg(x_236, x_237, x_238, x_239);
lean_dec(x_239);
lean_dec_ref(x_238);
lean_dec(x_237);
lean_dec_ref(x_236);
return x_254;
}
else
{
lean_object* x_255; lean_object* x_256; 
x_255 = l_Lean_Syntax_getArg(x_251, x_94);
lean_dec(x_251);
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_255);
x_210 = x_242;
x_211 = x_247;
x_212 = x_232;
x_213 = x_240;
x_214 = x_250;
x_215 = x_256;
x_216 = x_233;
x_217 = x_234;
x_218 = x_235;
x_219 = x_236;
x_220 = x_237;
x_221 = x_238;
x_222 = x_239;
goto block_231;
}
}
else
{
lean_object* x_257; 
lean_dec(x_251);
x_257 = lean_box(0);
x_210 = x_242;
x_211 = x_247;
x_212 = x_232;
x_213 = x_240;
x_214 = x_250;
x_215 = x_257;
x_216 = x_233;
x_217 = x_234;
x_218 = x_235;
x_219 = x_236;
x_220 = x_237;
x_221 = x_238;
x_222 = x_239;
goto block_231;
}
}
}
}
}
block_91:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = l_Array_append___redArg(x_81, x_84);
lean_dec_ref(x_84);
lean_inc(x_78);
x_86 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_86, 0, x_78);
lean_ctor_set(x_86, 1, x_80);
lean_ctor_set(x_86, 2, x_85);
x_87 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__32));
lean_inc(x_78);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_78);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_Syntax_node6(x_78, x_76, x_77, x_82, x_83, x_79, x_86, x_88);
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_303; uint8_t x_304; uint8_t x_315; 
x_268 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
x_269 = lean_unsigned_to_nat(0u);
x_303 = lean_array_get_size(x_268);
x_315 = lean_nat_dec_lt(x_269, x_303);
if (x_315 == 0)
{
x_304 = x_73;
goto block_314;
}
else
{
if (x_315 == 0)
{
x_304 = x_73;
goto block_314;
}
else
{
size_t x_316; size_t x_317; uint8_t x_318; 
x_316 = 0;
x_317 = lean_usize_of_nat(x_303);
x_318 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__16(x_268, x_316, x_317);
x_304 = x_318;
goto block_314;
}
}
block_302:
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_271 = lean_st_ref_get(x_7);
x_272 = lean_box(0);
x_273 = lean_array_get_borrowed(x_272, x_270, x_269);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_273);
x_274 = l_Lean_Elab_Term_CollectPatternVars_collect(x_273, x_7, x_8, x_9, x_4, x_5, x_10, x_11);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
lean_dec_ref(x_274);
x_276 = lean_st_ref_get(x_7);
x_277 = lean_unsigned_to_nat(1u);
x_278 = lean_mk_empty_array_with_capacity(x_277);
x_279 = lean_array_push(x_278, x_275);
x_280 = lean_array_get_size(x_270);
x_281 = l_Array_toSubarray___redArg(x_270, x_277, x_280);
lean_inc(x_7);
x_282 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__14___redArg(x_271, x_276, x_281, x_279, x_7, x_8, x_9, x_4, x_5, x_10, x_11);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; uint8_t x_285; uint8_t x_293; 
x_283 = lean_ctor_get(x_282, 0);
x_293 = !lean_is_exclusive(x_282);
if (x_293 == 0)
{
x_284 = x_282;
x_285 = x_293;
goto block_292;
}
else
{
lean_inc(x_283);
lean_dec(x_282);
x_284 = lean_box(0);
x_285 = x_293;
goto block_292;
}
block_292:
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_286 = lean_st_ref_set(x_7, x_276);
lean_dec(x_7);
x_287 = lean_box(2);
x_288 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_74);
lean_ctor_set(x_288, 2, x_283);
if (x_285 == 0)
{
lean_ctor_set(x_284, 0, x_288);
x_289 = x_284;
goto block_290;
}
else
{
lean_object* x_291; 
x_291 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_291, 0, x_288);
x_289 = x_291;
goto block_290;
}
block_290:
{
return x_289;
}
}
}
else
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; uint8_t x_301; 
lean_dec(x_276);
lean_dec(x_7);
x_294 = lean_ctor_get(x_282, 0);
x_301 = !lean_is_exclusive(x_282);
if (x_301 == 0)
{
x_295 = x_282;
x_296 = x_301;
goto block_300;
}
else
{
lean_inc(x_294);
lean_dec(x_282);
x_295 = lean_box(0);
x_296 = x_301;
goto block_300;
}
block_300:
{
lean_object* x_297; 
if (x_296 == 0)
{
x_297 = x_295;
goto block_298;
}
else
{
lean_object* x_299; 
x_299 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_299, 0, x_294);
x_297 = x_299;
goto block_298;
}
block_298:
{
return x_297;
}
}
}
}
else
{
lean_dec(x_271);
lean_dec_ref(x_270);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_274;
}
}
block_314:
{
if (x_304 == 0)
{
x_270 = x_268;
goto block_302;
}
else
{
lean_object* x_305; uint8_t x_306; 
x_305 = ((lean_object*)(l_Array_mapSepElemsM___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__17___closed__0));
x_306 = lean_nat_dec_lt(x_269, x_303);
if (x_306 == 0)
{
lean_dec_ref(x_268);
x_270 = x_305;
goto block_302;
}
else
{
uint8_t x_307; 
x_307 = lean_nat_dec_le(x_303, x_303);
if (x_307 == 0)
{
if (x_306 == 0)
{
lean_dec_ref(x_268);
x_270 = x_305;
goto block_302;
}
else
{
size_t x_308; size_t x_309; lean_object* x_310; 
x_308 = 0;
x_309 = lean_usize_of_nat(x_303);
x_310 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15(x_268, x_308, x_309, x_305);
lean_dec_ref(x_268);
x_270 = x_310;
goto block_302;
}
}
else
{
size_t x_311; size_t x_312; lean_object* x_313; 
x_311 = 0;
x_312 = lean_usize_of_nat(x_303);
x_313 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__15(x_268, x_311, x_312, x_305);
lean_dec_ref(x_268);
x_270 = x_313;
goto block_302;
}
}
}
}
}
}
else
{
lean_object* x_319; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
x_319 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_319, 0, x_3);
return x_319;
}
}
else
{
lean_object* x_320; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
x_320 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_320, 0, x_3);
return x_320;
}
}
else
{
lean_object* x_321; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
x_321 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_321, 0, x_3);
return x_321;
}
}
else
{
lean_object* x_322; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
x_322 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_322, 0, x_3);
return x_322;
}
}
else
{
lean_object* x_323; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
x_323 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_323, 0, x_3);
return x_323;
}
}
else
{
lean_object* x_324; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
x_324 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_324, 0, x_3);
return x_324;
}
}
else
{
lean_object* x_325; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
x_325 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_325, 0, x_3);
return x_325;
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_unsigned_to_nat(2u);
x_327 = l_Lean_Syntax_getArg(x_3, x_326);
x_328 = l_Lean_Elab_Term_CollectPatternVars_collect(x_327, x_7, x_8, x_9, x_4, x_5, x_10, x_11);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; uint8_t x_331; uint8_t x_337; 
x_329 = lean_ctor_get(x_328, 0);
x_337 = !lean_is_exclusive(x_328);
if (x_337 == 0)
{
x_330 = x_328;
x_331 = x_337;
goto block_336;
}
else
{
lean_inc(x_329);
lean_dec(x_328);
x_330 = lean_box(0);
x_331 = x_337;
goto block_336;
}
block_336:
{
lean_object* x_332; lean_object* x_333; 
x_332 = l_Lean_Syntax_setArg(x_3, x_326, x_329);
if (x_331 == 0)
{
lean_ctor_set(x_330, 0, x_332);
x_333 = x_330;
goto block_334;
}
else
{
lean_object* x_335; 
x_335 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_335, 0, x_332);
x_333 = x_335;
goto block_334;
}
block_334:
{
return x_333;
}
}
}
else
{
lean_dec(x_3);
return x_328;
}
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_338 = lean_unsigned_to_nat(1u);
x_339 = l_Lean_Syntax_getArg(x_3, x_338);
x_340 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processId___closed__0));
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
x_341 = l_Lean_Elab_Term_resolveId_x3f(x_339, x_340, x_55, x_8, x_9, x_4, x_5, x_10, x_11);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
lean_dec_ref(x_341);
if (lean_obj_tag(x_342) == 1)
{
lean_object* x_353; 
x_353 = lean_ctor_get(x_342, 0);
lean_inc(x_353);
lean_dec_ref(x_342);
if (lean_obj_tag(x_353) == 4)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
lean_dec_ref(x_353);
x_355 = lean_st_ref_get(x_11);
x_356 = lean_ctor_get(x_355, 0);
lean_inc_ref(x_356);
lean_dec(x_355);
x_357 = lean_has_match_pattern_attribute(x_356, x_354);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; 
x_358 = lean_box(0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
x_359 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg(x_358, x_7, x_8, x_9, x_4, x_5, x_10, x_11);
if (lean_obj_tag(x_359) == 0)
{
lean_dec_ref(x_359);
x_13 = x_7;
x_14 = x_8;
x_15 = x_9;
x_16 = x_4;
x_17 = x_5;
x_18 = x_10;
x_19 = x_11;
goto block_37;
}
else
{
lean_object* x_360; lean_object* x_361; uint8_t x_362; uint8_t x_367; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_360 = lean_ctor_get(x_359, 0);
x_367 = !lean_is_exclusive(x_359);
if (x_367 == 0)
{
x_361 = x_359;
x_362 = x_367;
goto block_366;
}
else
{
lean_inc(x_360);
lean_dec(x_359);
x_361 = lean_box(0);
x_362 = x_367;
goto block_366;
}
block_366:
{
lean_object* x_363; 
if (x_362 == 0)
{
x_363 = x_361;
goto block_364;
}
else
{
lean_object* x_365; 
x_365 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_365, 0, x_360);
x_363 = x_365;
goto block_364;
}
block_364:
{
return x_363;
}
}
}
}
else
{
x_13 = x_7;
x_14 = x_8;
x_15 = x_9;
x_16 = x_4;
x_17 = x_5;
x_18 = x_10;
x_19 = x_11;
goto block_37;
}
}
else
{
lean_dec(x_353);
lean_dec(x_3);
x_343 = x_7;
x_344 = x_8;
x_345 = x_9;
x_346 = x_4;
x_347 = x_5;
x_348 = x_10;
x_349 = x_11;
goto block_352;
}
}
else
{
lean_dec(x_342);
lean_dec(x_3);
x_343 = x_7;
x_344 = x_8;
x_345 = x_9;
x_346 = x_4;
x_347 = x_5;
x_348 = x_10;
x_349 = x_11;
goto block_352;
}
block_352:
{
lean_object* x_350; lean_object* x_351; 
x_350 = lean_box(0);
x_351 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg(x_350, x_343, x_344, x_345, x_346, x_347, x_348, x_349);
return x_351;
}
}
else
{
lean_object* x_368; lean_object* x_369; uint8_t x_370; uint8_t x_375; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_368 = lean_ctor_get(x_341, 0);
x_375 = !lean_is_exclusive(x_341);
if (x_375 == 0)
{
x_369 = x_341;
x_370 = x_375;
goto block_374;
}
else
{
lean_inc(x_368);
lean_dec(x_341);
x_369 = lean_box(0);
x_370 = x_375;
goto block_374;
}
block_374:
{
lean_object* x_371; 
if (x_370 == 0)
{
x_371 = x_369;
goto block_372;
}
else
{
lean_object* x_373; 
x_373 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_373, 0, x_368);
x_371 = x_373;
goto block_372;
}
block_372:
{
return x_371;
}
}
}
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_unsigned_to_nat(0u);
x_377 = l_Lean_Syntax_getArg(x_3, x_376);
lean_inc_ref(x_10);
lean_inc(x_377);
x_378 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar(x_377, x_7, x_8, x_9, x_4, x_5, x_10, x_11);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
lean_dec_ref(x_378);
x_413 = lean_unsigned_to_nat(2u);
x_414 = l_Lean_Syntax_getArg(x_3, x_413);
x_415 = l_Lean_Syntax_isNone(x_414);
if (x_415 == 0)
{
lean_object* x_416; 
x_416 = l_Lean_Syntax_getArg(x_414, x_376);
lean_dec(x_414);
x_379 = x_416;
x_380 = x_7;
x_381 = x_8;
x_382 = x_9;
x_383 = x_4;
x_384 = x_5;
x_385 = x_10;
x_386 = x_11;
goto block_412;
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_414);
x_417 = lean_ctor_get(x_10, 5);
x_418 = lean_ctor_get(x_10, 10);
x_419 = lean_ctor_get(x_10, 11);
x_420 = l_Lean_SourceInfo_fromRef(x_417, x_53);
x_421 = lean_obj_once(&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__51, &l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__51_once, _init_l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__51);
x_422 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__52));
lean_inc(x_419);
lean_inc(x_418);
x_423 = l_Lean_addMacroScope(x_418, x_422, x_419);
x_424 = lean_box(0);
x_425 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_425, 0, x_420);
lean_ctor_set(x_425, 1, x_421);
lean_ctor_set(x_425, 2, x_423);
lean_ctor_set(x_425, 3, x_424);
x_379 = x_425;
x_380 = x_7;
x_381 = x_8;
x_382 = x_9;
x_383 = x_4;
x_384 = x_5;
x_385 = x_10;
x_386 = x_11;
goto block_412;
}
block_412:
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_unsigned_to_nat(3u);
x_388 = l_Lean_Syntax_getArg(x_3, x_387);
lean_dec(x_3);
lean_inc(x_386);
lean_inc_ref(x_385);
lean_inc(x_384);
lean_inc_ref(x_383);
lean_inc(x_382);
lean_inc_ref(x_381);
lean_inc(x_380);
x_389 = l_Lean_Elab_Term_CollectPatternVars_collect(x_388, x_380, x_381, x_382, x_383, x_384, x_385, x_386);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
lean_dec_ref(x_389);
lean_inc_ref(x_385);
lean_inc(x_379);
x_391 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar(x_379, x_380, x_381, x_382, x_383, x_384, x_385, x_386);
lean_dec(x_386);
lean_dec(x_384);
lean_dec_ref(x_383);
lean_dec(x_382);
lean_dec_ref(x_381);
lean_dec(x_380);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; uint8_t x_393; uint8_t x_410; 
x_410 = !lean_is_exclusive(x_391);
if (x_410 == 0)
{
lean_object* x_411; 
x_411 = lean_ctor_get(x_391, 0);
lean_dec(x_411);
x_392 = x_391;
x_393 = x_410;
goto block_409;
}
else
{
lean_dec(x_391);
x_392 = lean_box(0);
x_393 = x_410;
goto block_409;
}
block_409:
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_394 = lean_ctor_get(x_385, 5);
lean_inc(x_394);
x_395 = lean_ctor_get(x_385, 10);
lean_inc(x_395);
x_396 = lean_ctor_get(x_385, 11);
lean_inc(x_396);
lean_dec_ref(x_385);
x_397 = l_Lean_SourceInfo_fromRef(x_394, x_53);
lean_dec(x_394);
x_398 = lean_obj_once(&l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__44, &l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__44_once, _init_l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__44);
x_399 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__46));
x_400 = l_Lean_addMacroScope(x_395, x_399, x_396);
x_401 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__49));
lean_inc(x_397);
x_402 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_402, 0, x_397);
lean_ctor_set(x_402, 1, x_398);
lean_ctor_set(x_402, 2, x_400);
lean_ctor_set(x_402, 3, x_401);
x_403 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__7));
lean_inc(x_397);
x_404 = l_Lean_Syntax_node3(x_397, x_403, x_377, x_390, x_379);
x_405 = l_Lean_Syntax_node2(x_397, x_38, x_402, x_404);
if (x_393 == 0)
{
lean_ctor_set(x_392, 0, x_405);
x_406 = x_392;
goto block_407;
}
else
{
lean_object* x_408; 
x_408 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_408, 0, x_405);
x_406 = x_408;
goto block_407;
}
block_407:
{
return x_406;
}
}
}
else
{
lean_dec(x_390);
lean_dec_ref(x_385);
lean_dec(x_379);
lean_dec(x_377);
return x_391;
}
}
else
{
lean_dec(x_386);
lean_dec_ref(x_385);
lean_dec(x_384);
lean_dec_ref(x_383);
lean_dec(x_382);
lean_dec_ref(x_381);
lean_dec(x_380);
lean_dec(x_379);
lean_dec(x_377);
return x_389;
}
}
}
else
{
lean_dec(x_377);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_378;
}
}
}
else
{
lean_object* x_426; 
x_426 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtor(x_3, x_7, x_8, x_9, x_4, x_5, x_10, x_11);
return x_426;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_unsigned_to_nat(0u);
x_428 = l_Lean_Syntax_getArg(x_3, x_427);
lean_dec(x_3);
x_429 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtor(x_428, x_7, x_8, x_9, x_4, x_5, x_10, x_11);
return x_429;
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_430 = lean_unsigned_to_nat(1u);
x_431 = l_Lean_Syntax_getArg(x_3, x_430);
x_432 = l_Lean_Elab_Term_CollectPatternVars_collect(x_431, x_7, x_8, x_9, x_4, x_5, x_10, x_11);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; lean_object* x_434; uint8_t x_435; uint8_t x_441; 
x_433 = lean_ctor_get(x_432, 0);
x_441 = !lean_is_exclusive(x_432);
if (x_441 == 0)
{
x_434 = x_432;
x_435 = x_441;
goto block_440;
}
else
{
lean_inc(x_433);
lean_dec(x_432);
x_434 = lean_box(0);
x_435 = x_441;
goto block_440;
}
block_440:
{
lean_object* x_436; lean_object* x_437; 
x_436 = l_Lean_Syntax_setArg(x_3, x_430, x_433);
if (x_435 == 0)
{
lean_ctor_set(x_434, 0, x_436);
x_437 = x_434;
goto block_438;
}
else
{
lean_object* x_439; 
x_439 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_439, 0, x_436);
x_437 = x_439;
goto block_438;
}
block_438:
{
return x_437;
}
}
}
else
{
lean_dec(x_3);
return x_432;
}
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
x_442 = lean_ctor_get(x_10, 5);
lean_inc(x_442);
lean_dec_ref(x_10);
x_443 = l_Lean_SourceInfo_fromRef(x_442, x_45);
lean_dec(x_442);
x_444 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__17));
x_445 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__53));
lean_inc(x_443);
x_446 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_446, 0, x_443);
lean_ctor_set(x_446, 1, x_445);
x_447 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__5));
lean_inc(x_443);
x_448 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_448, 0, x_443);
lean_ctor_set(x_448, 1, x_447);
x_449 = l_Lean_Syntax_node3(x_443, x_444, x_446, x_3, x_448);
x_450 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_450, 0, x_449);
return x_450;
}
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
x_451 = lean_ctor_get(x_10, 5);
lean_inc(x_451);
lean_dec_ref(x_10);
x_452 = l_Lean_SourceInfo_fromRef(x_451, x_43);
lean_dec(x_451);
x_453 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__17));
x_454 = ((lean_object*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___closed__53));
lean_inc(x_452);
x_455 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_455, 0, x_452);
lean_ctor_set(x_455, 1, x_454);
x_456 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___closed__5));
lean_inc(x_452);
x_457 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_457, 0, x_452);
lean_ctor_set(x_457, 1, x_456);
x_458 = l_Lean_Syntax_node3(x_452, x_453, x_455, x_3, x_457);
x_459 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_459, 0, x_458);
return x_459;
}
}
else
{
lean_object* x_460; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
x_460 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_460, 0, x_3);
return x_460;
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_461 = lean_unsigned_to_nat(1u);
x_462 = l_Lean_Syntax_getArg(x_3, x_461);
x_463 = l_Lean_Syntax_getArgs(x_462);
lean_dec(x_462);
x_464 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___boxed), 9, 0);
x_465 = l_Array_mapSepElemsM___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__17(x_463, x_464, x_7, x_8, x_9, x_4, x_5, x_10, x_11);
lean_dec_ref(x_463);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; uint8_t x_468; uint8_t x_477; 
x_466 = lean_ctor_get(x_465, 0);
x_477 = !lean_is_exclusive(x_465);
if (x_477 == 0)
{
x_467 = x_465;
x_468 = x_477;
goto block_476;
}
else
{
lean_inc(x_466);
lean_dec(x_465);
x_467 = lean_box(0);
x_468 = x_477;
goto block_476;
}
block_476:
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_469 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___closed__7));
x_470 = lean_box(2);
x_471 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_471, 0, x_470);
lean_ctor_set(x_471, 1, x_469);
lean_ctor_set(x_471, 2, x_466);
x_472 = l_Lean_Syntax_setArg(x_3, x_461, x_471);
if (x_468 == 0)
{
lean_ctor_set(x_467, 0, x_472);
x_473 = x_467;
goto block_474;
}
else
{
lean_object* x_475; 
x_475 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_475, 0, x_472);
x_473 = x_475;
goto block_474;
}
block_474:
{
return x_473;
}
}
}
else
{
lean_object* x_478; lean_object* x_479; uint8_t x_480; uint8_t x_485; 
lean_dec(x_3);
x_478 = lean_ctor_get(x_465, 0);
x_485 = !lean_is_exclusive(x_465);
if (x_485 == 0)
{
x_479 = x_465;
x_480 = x_485;
goto block_484;
}
else
{
lean_inc(x_478);
lean_dec(x_465);
x_479 = lean_box(0);
x_480 = x_485;
goto block_484;
}
block_484:
{
lean_object* x_481; 
if (x_480 == 0)
{
x_481 = x_479;
goto block_482;
}
else
{
lean_object* x_483; 
x_483 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_483, 0, x_478);
x_481 = x_483;
goto block_482;
}
block_482:
{
return x_481;
}
}
}
}
}
else
{
lean_object* x_486; 
x_486 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp(x_3, x_7, x_8, x_9, x_4, x_5, x_10, x_11);
lean_dec(x_3);
return x_486;
}
}
else
{
lean_object* x_487; 
x_487 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processId(x_3, x_7, x_8, x_9, x_4, x_5, x_10, x_11);
return x_487;
}
block_37:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(2u);
x_21 = l_Lean_Syntax_getArg(x_3, x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
x_22 = l_Lean_Elab_Term_CollectPatternVars_collect(x_21, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_unsigned_to_nat(3u);
x_25 = l_Lean_Syntax_getArg(x_3, x_24);
x_26 = l_Lean_Elab_Term_CollectPatternVars_collect(x_25, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_36; 
x_27 = lean_ctor_get(x_26, 0);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
x_28 = x_26;
x_29 = x_36;
goto block_35;
}
else
{
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Lean_Syntax_setArg(x_3, x_20, x_23);
x_31 = l_Lean_Syntax_setArg(x_30, x_24, x_27);
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_31);
x_32 = x_28;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
else
{
lean_dec(x_23);
lean_dec(x_3);
return x_26;
}
}
else
{
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_3);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
x_14 = lean_unbox(x_6);
x_15 = l_Lean_Elab_Term_CollectPatternVars_collect___lam__0(x_13, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_41; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_7, 2);
x_13 = lean_ctor_get(x_7, 3);
x_14 = lean_ctor_get(x_7, 4);
x_15 = lean_ctor_get(x_7, 5);
x_16 = lean_ctor_get(x_7, 6);
x_17 = lean_ctor_get(x_7, 7);
x_18 = lean_ctor_get(x_7, 8);
x_19 = lean_ctor_get(x_7, 9);
x_20 = lean_ctor_get(x_7, 10);
x_21 = lean_ctor_get(x_7, 11);
x_22 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_23 = lean_ctor_get(x_7, 12);
x_24 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_25 = lean_ctor_get(x_7, 13);
x_41 = !lean_is_exclusive(x_7);
if (x_41 == 0)
{
x_26 = x_7;
x_27 = x_41;
goto block_40;
}
else
{
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_7);
x_26 = lean_box(0);
x_27 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc(x_1);
x_28 = l_Lean_Syntax_getKind(x_1);
x_29 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__2));
x_30 = lean_name_eq(x_28, x_29);
x_31 = 1;
x_32 = lean_box(x_30);
x_33 = lean_box(x_31);
lean_inc(x_1);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lam__0___boxed), 12, 9);
lean_closure_set(x_34, 0, x_32);
lean_closure_set(x_34, 1, x_28);
lean_closure_set(x_34, 2, x_1);
lean_closure_set(x_34, 3, x_5);
lean_closure_set(x_34, 4, x_6);
lean_closure_set(x_34, 5, x_33);
lean_closure_set(x_34, 6, x_2);
lean_closure_set(x_34, 7, x_3);
lean_closure_set(x_34, 8, x_4);
x_35 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
lean_dec(x_1);
if (x_27 == 0)
{
lean_ctor_set(x_26, 5, x_35);
x_36 = x_26;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_39, 0, x_10);
lean_ctor_set(x_39, 1, x_11);
lean_ctor_set(x_39, 2, x_12);
lean_ctor_set(x_39, 3, x_13);
lean_ctor_set(x_39, 4, x_14);
lean_ctor_set(x_39, 5, x_35);
lean_ctor_set(x_39, 6, x_16);
lean_ctor_set(x_39, 7, x_17);
lean_ctor_set(x_39, 8, x_18);
lean_ctor_set(x_39, 9, x_19);
lean_ctor_set(x_39, 10, x_20);
lean_ctor_set(x_39, 11, x_21);
lean_ctor_set(x_39, 12, x_23);
lean_ctor_set(x_39, 13, x_25);
lean_ctor_set_uint8(x_39, sizeof(void*)*14, x_22);
lean_ctor_set_uint8(x_39, sizeof(void*)*14 + 1, x_24);
x_36 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_37; 
x_37 = l_Lean_Core_withFreshMacroScope___redArg(x_34, x_36, x_8);
return x_37;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__2));
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(356u);
x_4 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
if (lean_obj_tag(x_3) == 0)
{
if (x_1 == 0)
{
lean_object* x_33; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_33 = lean_ctor_get(x_3, 0);
lean_inc(x_33);
lean_dec_ref(x_3);
x_12 = x_33;
goto block_32;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
lean_dec_ref(x_3);
x_35 = l_Lean_Elab_Term_CollectPatternVars_collect(x_34, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_12 = x_36;
goto block_32;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec_ref(x_2);
x_37 = lean_ctor_get(x_35, 0);
x_44 = !lean_is_exclusive(x_35);
if (x_44 == 0)
{
x_38 = x_35;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_45 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__3, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__3_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__3);
x_46 = l_panic___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg_spec__11(x_45, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_46;
}
block_32:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_31; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*8 + 1);
x_17 = lean_ctor_get(x_2, 2);
x_18 = lean_ctor_get(x_2, 3);
x_19 = lean_ctor_get(x_2, 4);
x_20 = lean_ctor_get(x_2, 5);
x_21 = lean_ctor_get(x_2, 6);
x_22 = lean_ctor_get(x_2, 7);
x_31 = !lean_is_exclusive(x_2);
if (x_31 == 0)
{
x_23 = x_2;
x_24 = x_31;
goto block_30;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_array_push(x_22, x_12);
if (x_24 == 0)
{
lean_ctor_set(x_23, 7, x_25);
x_26 = x_23;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_14);
lean_ctor_set(x_29, 2, x_17);
lean_ctor_set(x_29, 3, x_18);
lean_ctor_set(x_29, 4, x_19);
lean_ctor_set(x_29, 5, x_20);
lean_ctor_set(x_29, 6, x_21);
lean_ctor_set(x_29, 7, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*8, x_15);
lean_ctor_set_uint8(x_29, sizeof(void*)*8 + 1, x_16);
x_26 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_2, 6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*8 + 1);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg(x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_8, 5);
x_15 = 0;
x_16 = l_Lean_SourceInfo_fromRef(x_14, x_15);
x_17 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___closed__1));
x_18 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___closed__2));
lean_inc(x_16);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Syntax_node1(x_16, x_17, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg(x_1, x_2, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_41; 
lean_inc_ref(x_11);
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
x_26 = lean_ctor_get_uint8(x_2, sizeof(void*)*8 + 1);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_ctor_get(x_2, 3);
x_29 = lean_ctor_get(x_2, 4);
x_30 = lean_ctor_get(x_2, 5);
x_31 = lean_ctor_get(x_2, 7);
x_41 = !lean_is_exclusive(x_2);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_2, 6);
lean_dec(x_42);
x_32 = x_2;
x_33 = x_41;
goto block_40;
}
else
{
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_32 = lean_box(0);
x_33 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_11, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_dec_ref(x_11);
if (x_33 == 0)
{
lean_ctor_set(x_32, 6, x_35);
x_36 = x_32;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_39, 0, x_23);
lean_ctor_set(x_39, 1, x_24);
lean_ctor_set(x_39, 2, x_27);
lean_ctor_set(x_39, 3, x_28);
lean_ctor_set(x_39, 4, x_29);
lean_ctor_set(x_39, 5, x_30);
lean_ctor_set(x_39, 6, x_35);
lean_ctor_set(x_39, 7, x_31);
lean_ctor_set_uint8(x_39, sizeof(void*)*8, x_25);
lean_ctor_set_uint8(x_39, sizeof(void*)*8 + 1, x_26);
x_36 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_37; 
x_37 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg(x_1, x_36, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_8, 5);
x_13 = l_Lean_SourceInfo_fromRef(x_12, x_11);
x_14 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___closed__1));
x_15 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___closed__2));
lean_inc(x_13);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Syntax_node1(x_13, x_14, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg(x_1, x_2, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isDone(x_1);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_11 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isNextArgAccessible(x_1);
x_12 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_getNextParam(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
x_36 = lean_ctor_get_uint8(x_14, sizeof(void*)*8);
x_37 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 1);
x_38 = lean_ctor_get(x_14, 2);
x_39 = lean_ctor_get(x_14, 3);
x_40 = lean_ctor_get(x_14, 4);
x_41 = lean_ctor_get(x_14, 5);
x_42 = lean_ctor_get(x_14, 6);
x_43 = lean_ctor_get(x_14, 7);
lean_inc(x_13);
x_44 = lean_alloc_closure((void*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext___lam__0___boxed), 2, 1);
lean_closure_set(x_44, 0, x_13);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), x_44, x_40, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_13, 1);
lean_inc(x_47);
lean_dec(x_13);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
switch (x_48) {
case 1:
{
x_15 = x_2;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
goto block_33;
}
case 2:
{
x_15 = x_2;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
goto block_33;
}
case 3:
{
x_15 = x_2;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
goto block_33;
}
default: 
{
lean_object* x_49; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_49 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg(x_11, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_1 = x_50;
goto _start;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_59; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_52 = lean_ctor_get(x_49, 0);
x_59 = !lean_is_exclusive(x_49);
if (x_59 == 0)
{
x_53 = x_49;
x_54 = x_59;
goto block_58;
}
else
{
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_box(0);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_54 == 0)
{
x_55 = x_53;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_52);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
}
}
else
{
lean_object* x_60; uint8_t x_61; uint8_t x_84; 
lean_inc_ref(x_43);
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc_ref(x_40);
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_13);
x_84 = !lean_is_exclusive(x_14);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_85 = lean_ctor_get(x_14, 7);
lean_dec(x_85);
x_86 = lean_ctor_get(x_14, 6);
lean_dec(x_86);
x_87 = lean_ctor_get(x_14, 5);
lean_dec(x_87);
x_88 = lean_ctor_get(x_14, 4);
lean_dec(x_88);
x_89 = lean_ctor_get(x_14, 3);
lean_dec(x_89);
x_90 = lean_ctor_get(x_14, 2);
lean_dec(x_90);
x_91 = lean_ctor_get(x_14, 1);
lean_dec(x_91);
x_92 = lean_ctor_get(x_14, 0);
lean_dec(x_92);
x_60 = x_14;
x_61 = x_84;
goto block_83;
}
else
{
lean_dec(x_14);
x_60 = lean_box(0);
x_61 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_46, 0);
lean_inc(x_62);
lean_dec_ref(x_46);
x_63 = lean_array_fget_borrowed(x_40, x_62);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 2);
lean_inc_ref(x_65);
x_66 = l_Array_eraseIdx___redArg(x_40, x_62);
x_67 = lean_box(0);
x_68 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount_checkNamedArgs_spec__0___redArg(x_41, x_64, x_67);
if (x_61 == 0)
{
lean_ctor_set(x_60, 5, x_68);
lean_ctor_set(x_60, 4, x_66);
x_69 = x_60;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_82, 0, x_34);
lean_ctor_set(x_82, 1, x_35);
lean_ctor_set(x_82, 2, x_38);
lean_ctor_set(x_82, 3, x_39);
lean_ctor_set(x_82, 4, x_66);
lean_ctor_set(x_82, 5, x_68);
lean_ctor_set(x_82, 6, x_42);
lean_ctor_set(x_82, 7, x_43);
lean_ctor_set_uint8(x_82, sizeof(void*)*8, x_36);
lean_ctor_set_uint8(x_82, sizeof(void*)*8 + 1, x_37);
x_69 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_70; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_70 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg(x_11, x_69, x_65, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
x_1 = x_71;
goto _start;
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_73 = lean_ctor_get(x_70, 0);
x_80 = !lean_is_exclusive(x_70);
if (x_80 == 0)
{
x_74 = x_70;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
}
}
block_33:
{
lean_object* x_22; 
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
x_22 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg(x_11, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_1 = x_23;
x_2 = x_15;
x_3 = x_16;
x_4 = x_17;
x_5 = x_18;
x_6 = x_19;
x_7 = x_20;
x_8 = x_21;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
x_25 = lean_ctor_get(x_22, 0);
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
x_26 = x_22;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
else
{
lean_object* x_93; 
x_93 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_93;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_111; uint8_t x_112; 
x_24 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__0));
x_25 = lean_array_to_list(x_3);
x_111 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__0___closed__2));
lean_inc(x_1);
x_112 = l_Lean_Syntax_isOfKind(x_1, x_111);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__4));
lean_inc(x_1);
x_114 = l_Lean_Syntax_isOfKind(x_1, x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__2, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__2_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__2);
x_116 = l_Lean_MessageData_ofSyntax(x_1);
x_117 = l_Lean_indentD(x_116);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1___redArg(x_118, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
x_99 = x_120;
x_100 = x_5;
x_101 = x_6;
x_102 = x_7;
x_103 = x_8;
x_104 = x_9;
x_105 = x_10;
x_106 = x_11;
goto block_110;
}
else
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_128; 
lean_dec(x_25);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_121 = lean_ctor_get(x_119, 0);
x_128 = !lean_is_exclusive(x_119);
if (x_128 == 0)
{
x_122 = x_119;
x_123 = x_128;
goto block_127;
}
else
{
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_box(0);
x_123 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_124; 
if (x_123 == 0)
{
x_124 = x_122;
goto block_125;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_121);
x_124 = x_126;
goto block_125;
}
block_125:
{
return x_124;
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_129 = lean_unsigned_to_nat(1u);
x_130 = l_Lean_Syntax_getArg(x_1, x_129);
lean_inc(x_130);
x_131 = l_Lean_Syntax_isOfKind(x_130, x_111);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_130);
x_132 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__2, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__2_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__2);
x_133 = l_Lean_MessageData_ofSyntax(x_1);
x_134 = l_Lean_indentD(x_133);
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1___redArg(x_135, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec_ref(x_136);
x_99 = x_137;
x_100 = x_5;
x_101 = x_6;
x_102 = x_7;
x_103 = x_8;
x_104 = x_9;
x_105 = x_10;
x_106 = x_11;
goto block_110;
}
else
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_145; 
lean_dec(x_25);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_138 = lean_ctor_get(x_136, 0);
x_145 = !lean_is_exclusive(x_136);
if (x_145 == 0)
{
x_139 = x_136;
x_140 = x_145;
goto block_144;
}
else
{
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_box(0);
x_140 = x_145;
goto block_144;
}
block_144:
{
lean_object* x_141; 
if (x_140 == 0)
{
x_141 = x_139;
goto block_142;
}
else
{
lean_object* x_143; 
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_138);
x_141 = x_143;
goto block_142;
}
block_142:
{
return x_141;
}
}
}
}
else
{
lean_dec(x_1);
x_26 = x_130;
x_27 = x_131;
x_28 = x_5;
x_29 = x_6;
x_30 = x_7;
x_31 = x_8;
x_32 = x_9;
x_33 = x_10;
x_34 = x_11;
goto block_98;
}
}
}
else
{
uint8_t x_146; 
x_146 = 0;
x_26 = x_1;
x_27 = x_146;
x_28 = x_5;
x_29 = x_6;
x_30 = x_7;
x_31 = x_8;
x_32 = x_9;
x_33 = x_10;
x_34 = x_11;
goto block_98;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_13);
x_22 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg(x_21, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_22;
}
block_98:
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_35 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processId___closed__0));
x_36 = 1;
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc(x_26);
x_37 = l_Lean_Elab_Term_resolveId_x3f(x_26, x_35, x_36, x_29, x_30, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
if (lean_obj_tag(x_38) == 1)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_89; 
x_39 = lean_ctor_get(x_38, 0);
x_89 = !lean_is_exclusive(x_38);
if (x_89 == 0)
{
x_40 = x_38;
x_41 = x_89;
goto block_88;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_89;
goto block_88;
}
block_88:
{
if (lean_obj_tag(x_39) == 4)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
lean_dec_ref(x_39);
lean_inc_ref(x_33);
lean_inc(x_42);
x_43 = l_Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6(x_42, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_Lean_ConstantInfo_type(x_44);
x_46 = 0;
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc_ref(x_29);
lean_inc(x_28);
x_47 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__7___redArg(x_45, x_24, x_46, x_46, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_47) == 0)
{
if (lean_obj_tag(x_44) == 6)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_42);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = lean_ctor_get(x_44, 0);
lean_inc_ref(x_49);
lean_dec_ref(x_44);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_49);
x_50 = x_40;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_49);
x_50 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_obj_once(&l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__2, &l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__2_once, _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__2);
x_53 = ((lean_object*)(l_Array_mapSepElemsM___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__17___closed__0));
x_54 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_54, 0, x_26);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_48);
lean_ctor_set(x_54, 3, x_51);
lean_ctor_set(x_54, 4, x_2);
lean_ctor_set(x_54, 5, x_52);
lean_ctor_set(x_54, 6, x_25);
lean_ctor_set(x_54, 7, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*8, x_27);
lean_ctor_set_uint8(x_54, sizeof(void*)*8 + 1, x_4);
x_55 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext(x_54, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
return x_55;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_44);
x_58 = lean_ctor_get(x_47, 0);
lean_inc(x_58);
lean_dec_ref(x_47);
x_59 = lean_st_ref_get(x_34);
x_60 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_60);
lean_dec(x_59);
x_61 = lean_has_match_pattern_attribute(x_60, x_42);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_58);
lean_dec(x_25);
lean_dec_ref(x_2);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_26);
x_62 = x_40;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_26);
x_62 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_63; 
x_63 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___redArg(x_62, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
return x_63;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_del_object(x_40);
x_66 = lean_box(0);
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_obj_once(&l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__2, &l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__2_once, _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default___closed__2);
x_69 = ((lean_object*)(l_Array_mapSepElemsM___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__17___closed__0));
x_70 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_70, 0, x_26);
lean_ctor_set(x_70, 1, x_66);
lean_ctor_set(x_70, 2, x_58);
lean_ctor_set(x_70, 3, x_67);
lean_ctor_set(x_70, 4, x_2);
lean_ctor_set(x_70, 5, x_68);
lean_ctor_set(x_70, 6, x_25);
lean_ctor_set(x_70, 7, x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*8, x_27);
lean_ctor_set_uint8(x_70, sizeof(void*)*8 + 1, x_4);
x_71 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext(x_70, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_79; 
lean_dec(x_44);
lean_dec(x_42);
lean_del_object(x_40);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_2);
x_72 = lean_ctor_get(x_47, 0);
x_79 = !lean_is_exclusive(x_47);
if (x_79 == 0)
{
x_73 = x_47;
x_74 = x_79;
goto block_78;
}
else
{
lean_inc(x_72);
lean_dec(x_47);
x_73 = lean_box(0);
x_74 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_75; 
if (x_74 == 0)
{
x_75 = x_73;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_72);
x_75 = x_77;
goto block_76;
}
block_76:
{
return x_75;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_87; 
lean_dec(x_42);
lean_del_object(x_40);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_2);
x_80 = lean_ctor_get(x_43, 0);
x_87 = !lean_is_exclusive(x_43);
if (x_87 == 0)
{
x_81 = x_43;
x_82 = x_87;
goto block_86;
}
else
{
lean_inc(x_80);
lean_dec(x_43);
x_81 = lean_box(0);
x_82 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_83; 
if (x_82 == 0)
{
x_83 = x_81;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_80);
x_83 = x_85;
goto block_84;
}
block_84:
{
return x_83;
}
}
}
}
else
{
lean_del_object(x_40);
lean_dec(x_39);
lean_dec(x_25);
lean_dec_ref(x_2);
x_13 = x_26;
x_14 = x_28;
x_15 = x_29;
x_16 = x_30;
x_17 = x_31;
x_18 = x_32;
x_19 = x_33;
x_20 = x_34;
goto block_23;
}
}
}
else
{
lean_dec(x_38);
lean_dec(x_25);
lean_dec_ref(x_2);
x_13 = x_26;
x_14 = x_28;
x_15 = x_29;
x_16 = x_30;
x_17 = x_31;
x_18 = x_32;
x_19 = x_33;
x_20 = x_34;
goto block_23;
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_97; 
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_2);
x_90 = lean_ctor_get(x_37, 0);
x_97 = !lean_is_exclusive(x_37);
if (x_97 == 0)
{
x_91 = x_37;
x_92 = x_97;
goto block_96;
}
else
{
lean_inc(x_90);
lean_dec(x_37);
x_91 = lean_box(0);
x_92 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_93; 
if (x_92 == 0)
{
x_93 = x_91;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_90);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
}
block_110:
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = lean_ctor_get(x_99, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_99, 1);
lean_inc(x_108);
lean_dec_ref(x_99);
x_109 = lean_unbox(x_108);
lean_dec(x_108);
x_26 = x_107;
x_27 = x_109;
x_28 = x_100;
x_29 = x_101;
x_30 = x_102;
x_31 = x_103;
x_32 = x_104;
x_33 = x_105;
x_34 = x_106;
goto block_98;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtor___closed__0));
x_11 = 0;
x_12 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore(x_1, x_10, x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_pushNewArg(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__3(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__14___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__14___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorApp_spec__2(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_1);
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__13(x_13, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
x_14 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__7___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_4);
x_15 = lean_unbox(x_5);
x_16 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__7(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__5(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__5___redArg(x_1, x_2, x_3, x_7, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__5(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__14___redArg(x_1, x_2, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___redArg(x_1, x_2, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore_spec__6_spec__10_spec__16_spec__22_spec__26_spec__27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0___redArg(x_1, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg___closed__0(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_53; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1_spec__1(x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
x_11 = x_9;
x_12 = x_53;
goto block_52;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_51; 
x_13 = lean_st_ref_take(x_6);
x_14 = lean_ctor_get(x_13, 4);
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 5);
x_20 = lean_ctor_get(x_13, 6);
x_21 = lean_ctor_get(x_13, 7);
x_22 = lean_ctor_get(x_13, 8);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
x_23 = x_13;
x_24 = x_51;
goto block_50;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_14);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_51;
goto block_50;
}
block_50:
{
uint64_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_49; 
x_25 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_26 = lean_ctor_get(x_14, 0);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
x_27 = x_14;
x_28 = x_49;
goto block_48;
}
else
{
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = x_49;
goto block_48;
}
block_48:
{
double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg___closed__0);
x_30 = 0;
x_31 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__15));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg___closed__1));
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_10);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_26, x_35);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_36);
x_37 = x_27;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set_uint64(x_47, sizeof(void*)*1, x_25);
x_37 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_38; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_37);
x_38 = x_23;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_16);
lean_ctor_set(x_45, 2, x_17);
lean_ctor_set(x_45, 3, x_18);
lean_ctor_set(x_45, 4, x_37);
lean_ctor_set(x_45, 5, x_19);
lean_ctor_set(x_45, 6, x_20);
lean_ctor_set(x_45, 7, x_21);
lean_ctor_set(x_45, 8, x_22);
x_38 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_st_ref_set(x_6, x_38);
x_40 = lean_box(0);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_40);
x_41 = x_11;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_2, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__2));
x_15 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0___redArg(x_14, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_35; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_array_uget(x_3, x_2);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_3, x_2, x_18);
x_35 = lean_unbox(x_16);
lean_dec(x_16);
if (x_35 == 0)
{
lean_object* x_36; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_36 = l_Lean_Elab_Term_CollectPatternVars_collect(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_20 = x_36;
goto block_34;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___closed__4);
lean_inc(x_17);
x_38 = l_Lean_MessageData_ofSyntax(x_17);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg(x_14, x_39, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec_ref(x_40);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_41 = l_Lean_Elab_Term_CollectPatternVars_collect(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_20 = x_41;
goto block_34;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; 
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_42 = lean_ctor_get(x_40, 0);
x_49 = !lean_is_exclusive(x_40);
if (x_49 == 0)
{
x_43 = x_40;
x_44 = x_49;
goto block_48;
}
else
{
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_box(0);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_44 == 0)
{
x_45 = x_43;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_42);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
block_34:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = 1;
x_23 = lean_usize_add(x_2, x_22);
x_24 = lean_array_uset(x_19, x_2, x_21);
x_2 = x_23;
x_3 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec_ref(x_19);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_26 = lean_ctor_get(x_20, 0);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
x_27 = x_20;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_50 = lean_ctor_get(x_15, 0);
x_57 = !lean_is_exclusive(x_15);
if (x_57 == 0)
{
x_51 = x_15;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_15);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_50);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_main___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_39; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
x_39 = !lean_is_exclusive(x_1);
if (x_39 == 0)
{
x_14 = x_1;
x_15 = x_39;
goto block_38;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_39;
goto block_38;
}
block_38:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_array_size(x_11);
x_17 = 0;
x_18 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_CollectPatternVars_main_spec__2(x_16, x_17, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_29; 
x_19 = lean_ctor_get(x_18, 0);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
x_20 = x_18;
x_21 = x_29;
goto block_28;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_22; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 1, x_19);
x_22 = x_14;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_12);
lean_ctor_set(x_27, 3, x_13);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_22);
x_23 = x_20;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
lean_del_object(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
x_30 = lean_ctor_get(x_18, 0);
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
x_31 = x_18;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_18);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_main___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_CollectPatternVars_main___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_CollectPatternVars_main___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_CollectPatternVars_main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg(x_1, x_2, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Term_collectPatternVars___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Array_mapSepElemsM___at___00Lean_Elab_Term_CollectPatternVars_collect_spec__17___closed__0));
x_2 = l_Lean_NameSet_empty;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_collectPatternVars___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_obj_once(&l_Lean_Elab_Term_collectPatternVars___redArg___closed__0, &l_Lean_Elab_Term_collectPatternVars___redArg___closed__0_once, _init_l_Lean_Elab_Term_collectPatternVars___redArg___closed__0);
x_10 = lean_st_mk_ref(x_9);
lean_inc(x_10);
x_11 = l_Lean_Elab_Term_CollectPatternVars_main___redArg(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_29; 
x_12 = lean_ctor_get(x_11, 0);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
x_13 = x_11;
x_14 = x_29;
goto block_28;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_26; 
x_15 = lean_st_ref_get(x_10);
lean_dec(x_10);
x_16 = lean_ctor_get(x_15, 1);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_15, 0);
lean_dec(x_27);
x_17 = x_15;
x_18 = x_26;
goto block_25;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_19; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 0, x_16);
x_19 = x_17;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_12);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_19);
x_20 = x_13;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
lean_dec(x_10);
x_30 = lean_ctor_get(x_11, 0);
x_37 = !lean_is_exclusive(x_11);
if (x_37 == 0)
{
x_31 = x_11;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_11);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_collectPatternVars___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_collectPatternVars___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_collectPatternVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_collectPatternVars___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_collectPatternVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_collectPatternVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_getPatternVars___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = ((lean_object*)(l_Lean_Elab_Term_getPatternVars___lam__0___closed__1));
x_3 = lean_name_eq(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternVars___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_getPatternVars___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__3(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveNamespace(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6_spec__10___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6_spec__10___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_20; 
x_20 = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs_spec__0___redArg___closed__0);
x_5 = x_20;
goto block_19;
}
else
{
uint64_t x_21; 
x_21 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_5 = x_21;
goto block_19;
}
block_19:
{
uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6_spec__10___redArg(x_2, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = l_Lean_instBEqExtraModUse_beq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11_spec__15___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11___redArg___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11___redArg___closed__1(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11___redArg___closed__0);
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11___redArg___closed__1);
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_instBEqExtraModUse_beq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_instHashableExtraModUse_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7___redArg(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_53; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1_spec__1(x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
x_11 = x_9;
x_12 = x_53;
goto block_52;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_51; 
x_13 = lean_st_ref_take(x_6);
x_14 = lean_ctor_get(x_13, 4);
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 5);
x_20 = lean_ctor_get(x_13, 6);
x_21 = lean_ctor_get(x_13, 7);
x_22 = lean_ctor_get(x_13, 8);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
x_23 = x_13;
x_24 = x_51;
goto block_50;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_14);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_51;
goto block_50;
}
block_50:
{
uint64_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_49; 
x_25 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_26 = lean_ctor_get(x_14, 0);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
x_27 = x_14;
x_28 = x_49;
goto block_48;
}
else
{
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = x_49;
goto block_48;
}
block_48:
{
double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg___closed__0);
x_30 = 0;
x_31 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__15));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg___closed__1));
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_10);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_26, x_35);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_36);
x_37 = x_27;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set_uint64(x_47, sizeof(void*)*1, x_25);
x_37 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_38; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_37);
x_38 = x_23;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_16);
lean_ctor_set(x_45, 2, x_17);
lean_ctor_set(x_45, 3, x_18);
lean_ctor_set(x_45, 4, x_37);
lean_ctor_set(x_45, 5, x_19);
lean_ctor_set(x_45, 6, x_20);
lean_ctor_set(x_45, 7, x_21);
lean_ctor_set(x_45, 8, x_22);
x_38 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_st_ref_set(x_6, x_38);
x_40 = lean_box(0);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_40);
x_41 = x_11;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__1));
x_2 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__0));
x_3 = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__3(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__3);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__4);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__4);
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__9));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__11));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwWrongArgCount___redArg___closed__15));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__14));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_63; uint8_t x_64; 
x_11 = lean_st_ref_get(x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*8);
lean_dec_ref(x_12);
x_14 = lean_st_ref_get(x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__2);
lean_inc(x_1);
x_17 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_13);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 1, x_2);
x_18 = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
x_19 = lean_box(1);
x_20 = lean_box(0);
x_63 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_16, x_18, x_15, x_19, x_20);
x_64 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7___redArg(x_63, x_17);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_73; lean_object* x_74; uint8_t x_87; 
x_65 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__8));
x_66 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__0___redArg(x_65, x_8);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_87 = lean_unbox(x_67);
lean_dec(x_67);
if (x_87 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
x_21 = x_7;
x_22 = x_9;
goto block_62;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__15);
if (x_13 == 0)
{
lean_object* x_97; 
x_97 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__18));
x_89 = x_97;
goto block_96;
}
else
{
lean_object* x_98; 
x_98 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__19));
x_89 = x_98;
goto block_96;
}
block_96:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = l_Lean_stringToMessageData(x_89);
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__3, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__3_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__3);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
if (x_2 == 0)
{
lean_object* x_94; 
x_94 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__16));
x_73 = x_93;
x_74 = x_94;
goto block_86;
}
else
{
lean_object* x_95; 
x_95 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__17));
x_73 = x_93;
x_74 = x_95;
goto block_86;
}
}
}
block_72:
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__1___redArg(x_65, x_70, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_71) == 0)
{
lean_dec_ref(x_71);
x_21 = x_7;
x_22 = x_9;
goto block_62;
}
else
{
lean_dec_ref(x_17);
return x_71;
}
}
block_86:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_75 = l_Lean_stringToMessageData(x_74);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__10);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_MessageData_ofName(x_1);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_Name_isAnonymous(x_3);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__12);
x_83 = l_Lean_MessageData_ofName(x_3);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_68 = x_80;
x_69 = x_84;
goto block_72;
}
else
{
lean_object* x_85; 
lean_dec(x_3);
x_85 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__13);
x_68 = x_80;
x_69 = x_85;
goto block_72;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec_ref(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
block_62:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_60; 
x_23 = lean_st_ref_take(x_22);
x_24 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_ctor_get(x_23, 2);
x_28 = lean_ctor_get(x_23, 3);
x_29 = lean_ctor_get(x_23, 4);
x_30 = lean_ctor_get(x_23, 6);
x_31 = lean_ctor_get(x_23, 7);
x_32 = lean_ctor_get(x_23, 8);
x_60 = !lean_is_exclusive(x_23);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_23, 5);
lean_dec(x_61);
x_33 = x_23;
x_34 = x_60;
goto block_59;
}
else
{
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_33 = lean_box(0);
x_34 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_24, 2);
lean_inc(x_35);
lean_dec_ref(x_24);
x_36 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_18, x_25, x_17, x_35, x_20);
lean_dec(x_35);
x_37 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__5);
if (x_34 == 0)
{
lean_ctor_set(x_33, 5, x_37);
lean_ctor_set(x_33, 0, x_36);
x_38 = x_33;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_58, 0, x_36);
lean_ctor_set(x_58, 1, x_26);
lean_ctor_set(x_58, 2, x_27);
lean_ctor_set(x_58, 3, x_28);
lean_ctor_set(x_58, 4, x_29);
lean_ctor_set(x_58, 5, x_37);
lean_ctor_set(x_58, 6, x_30);
lean_ctor_set(x_58, 7, x_31);
lean_ctor_set(x_58, 8, x_32);
x_38 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_55; 
x_39 = lean_st_ref_set(x_22, x_38);
x_40 = lean_st_ref_take(x_21);
x_41 = lean_ctor_get(x_40, 0);
x_42 = lean_ctor_get(x_40, 2);
x_43 = lean_ctor_get(x_40, 3);
x_44 = lean_ctor_get(x_40, 4);
x_55 = !lean_is_exclusive(x_40);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_40, 1);
lean_dec(x_56);
x_45 = x_40;
x_46 = x_55;
goto block_54;
}
else
{
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_40);
x_45 = lean_box(0);
x_46 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__6);
if (x_46 == 0)
{
lean_ctor_set(x_45, 1, x_47);
x_48 = x_45;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_41);
lean_ctor_set(x_53, 1, x_47);
lean_ctor_set(x_53, 2, x_42);
lean_ctor_set(x_53, 3, x_43);
lean_ctor_set(x_53, 4, x_44);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_st_ref_set(x_21, x_48);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_16 = l_Lean_Environment_header(x_1);
x_17 = lean_ctor_get(x_16, 3);
lean_inc_ref(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_instInhabitedEffectiveImport_default;
x_19 = lean_array_uget_borrowed(x_3, x_5);
x_20 = lean_array_get(x_18, x_17, x_19);
lean_dec_ref(x_17);
x_21 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = 0;
lean_inc(x_2);
x_24 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4(x_22, x_23, x_2, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; size_t x_26; size_t x_27; 
lean_dec_ref(x_24);
x_25 = lean_box(0);
x_26 = 1;
x_27 = lean_usize_add(x_5, x_26);
x_5 = x_27;
x_6 = x_25;
goto _start;
}
else
{
lean_dec(x_2);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__5(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_16;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___closed__1));
x_2 = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___closed__0));
x_3 = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_14; lean_object* x_15; lean_object* x_29; 
x_10 = lean_st_ref_get(x_8);
x_14 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_14);
lean_dec(x_10);
x_29 = l_Lean_Environment_getModuleIdxFor_x3f(x_14, x_1);
if (lean_obj_tag(x_29) == 0)
{
lean_dec_ref(x_14);
lean_dec(x_1);
goto block_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l_Lean_Environment_header(x_14);
x_32 = lean_ctor_get(x_31, 3);
lean_inc_ref(x_32);
lean_dec_ref(x_31);
x_33 = lean_array_get_size(x_32);
x_34 = lean_nat_dec_lt(x_30, x_33);
if (x_34 == 0)
{
lean_dec_ref(x_32);
lean_dec(x_30);
lean_dec_ref(x_14);
lean_dec(x_1);
goto block_13;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_st_ref_get(x_8);
x_36 = lean_ctor_get(x_35, 0);
lean_inc_ref(x_36);
lean_dec(x_35);
x_37 = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___closed__2);
x_38 = lean_array_fget(x_32, x_30);
lean_dec(x_30);
lean_dec_ref(x_32);
if (x_2 == 0)
{
lean_dec_ref(x_36);
x_39 = x_2;
goto block_50;
}
else
{
uint8_t x_51; 
lean_inc(x_1);
x_51 = l_Lean_isMarkedMeta(x_36, x_1);
if (x_51 == 0)
{
x_39 = x_2;
goto block_50;
}
else
{
uint8_t x_52; 
x_52 = 0;
x_39 = x_52;
goto block_50;
}
}
block_50:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc_ref(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
lean_inc(x_1);
x_42 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4(x_41, x_39, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_42);
x_43 = l_Lean_indirectModUseExt;
x_44 = lean_box(1);
x_45 = lean_box(0);
lean_inc_ref(x_14);
x_46 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_37, x_43, x_14, x_44, x_45);
x_47 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6___redArg(x_46, x_1);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___closed__3));
x_15 = x_48;
goto block_28;
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec_ref(x_47);
x_15 = x_49;
goto block_28;
}
}
else
{
lean_dec_ref(x_14);
lean_dec(x_1);
return x_42;
}
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
block_28:
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_box(0);
x_17 = lean_array_size(x_15);
x_18 = 0;
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__5(x_14, x_1, x_15, x_17, x_18, x_16, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; uint8_t x_26; 
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
x_20 = x_19;
x_21 = x_26;
goto block_25;
}
else
{
lean_dec(x_19);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_16);
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_16);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
else
{
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = 1;
x_14 = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3(x_11, x_13, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec_ref(x_14);
x_15 = lean_box(0);
x_1 = x_12;
x_2 = x_15;
goto _start;
}
else
{
lean_dec(x_12);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__3);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__4);
x_2 = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__2));
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__5);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_28; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
lean_inc(x_13);
x_15 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__0___redArg(x_13, x_6);
x_16 = lean_ctor_get(x_15, 0);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
x_17 = x_15;
x_18 = x_28;
goto block_27;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_28;
goto block_27;
}
block_27:
{
uint8_t x_19; 
x_19 = lean_unbox(x_16);
lean_dec(x_16);
if (x_19 == 0)
{
lean_del_object(x_17);
lean_dec(x_14);
lean_dec(x_13);
x_1 = x_12;
goto _start;
}
else
{
lean_object* x_21; 
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 0, x_14);
x_21 = x_17;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_14);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_MessageData_ofFormat(x_21);
x_23 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__1___redArg(x_13, x_22, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_dec_ref(x_23);
x_1 = x_12;
goto _start;
}
else
{
lean_dec(x_12);
return x_23;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__8___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__8___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__8___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__8___redArg___closed__0);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__8___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__8___redArg();
return x_2;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__2));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_26; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
x_5 = x_2;
x_6 = x_26;
goto block_25;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_23; 
x_7 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_3, 1);
lean_dec(x_24);
x_8 = x_3;
x_9 = x_23;
goto block_22;
}
else
{
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__0);
if (x_9 == 0)
{
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_10);
lean_ctor_set(x_8, 0, x_1);
x_11 = x_8;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_10);
x_11 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__3);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_12);
lean_ctor_set(x_5, 0, x_11);
x_13 = x_5;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_12);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_MessageData_ofSyntax(x_7);
x_15 = l_Lean_indentD(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_1 = x_16;
x_2 = x_4;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__17(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__17___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__17(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___redArg___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lean_Elab_pp_macroStack;
x_7 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__17(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_26; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_10, 0);
lean_dec(x_27);
x_12 = x_10;
x_13 = x_26;
goto block_25;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18___closed__0);
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_14);
lean_ctor_set(x_12, 0, x_1);
x_15 = x_12;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_14);
x_15 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___redArg___closed__2);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_MessageData_ofSyntax(x_11);
x_19 = l_Lean_indentD(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15_spec__18(x_20, x_2);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_23; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected_spec__1_spec__1(x_1, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
lean_inc(x_12);
x_13 = l_Lean_Elab_getBetterRef(x_9, x_12);
x_14 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___redArg(x_11, x_12, x_6);
x_15 = lean_ctor_get(x_14, 0);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
x_16 = x_14;
x_17 = x_23;
goto block_22;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_15);
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_34; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_7, 2);
x_13 = lean_ctor_get(x_7, 3);
x_14 = lean_ctor_get(x_7, 4);
x_15 = lean_ctor_get(x_7, 5);
x_16 = lean_ctor_get(x_7, 6);
x_17 = lean_ctor_get(x_7, 7);
x_18 = lean_ctor_get(x_7, 8);
x_19 = lean_ctor_get(x_7, 9);
x_20 = lean_ctor_get(x_7, 10);
x_21 = lean_ctor_get(x_7, 11);
x_22 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_23 = lean_ctor_get(x_7, 12);
x_24 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_25 = lean_ctor_get(x_7, 13);
x_34 = !lean_is_exclusive(x_7);
if (x_34 == 0)
{
x_26 = x_7;
x_27 = x_34;
goto block_33;
}
else
{
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_7);
x_26 = lean_box(0);
x_27 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
if (x_27 == 0)
{
lean_ctor_set(x_26, 5, x_28);
x_29 = x_26;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_32, 0, x_10);
lean_ctor_set(x_32, 1, x_11);
lean_ctor_set(x_32, 2, x_12);
lean_ctor_set(x_32, 3, x_13);
lean_ctor_set(x_32, 4, x_14);
lean_ctor_set(x_32, 5, x_28);
lean_ctor_set(x_32, 6, x_16);
lean_ctor_set(x_32, 7, x_17);
lean_ctor_set(x_32, 8, x_18);
lean_ctor_set(x_32, 9, x_19);
lean_ctor_set(x_32, 10, x_20);
lean_ctor_set(x_32, 11, x_21);
lean_ctor_set(x_32, 12, x_23);
lean_ctor_set(x_32, 13, x_25);
lean_ctor_set_uint8(x_32, sizeof(void*)*14, x_22);
lean_ctor_set_uint8(x_32, sizeof(void*)*14 + 1, x_24);
x_29 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_30; 
x_30 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10___redArg(x_2, x_3, x_4, x_5, x_6, x_29, x_8);
lean_dec_ref(x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_ResolveName_resolveGlobalName(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_5 = 0;
x_6 = l_Lean_Environment_setExporting(x_1, x_5);
lean_inc(x_2);
x_7 = l_Lean_mkPrivateName(x_6, x_2);
x_8 = 1;
lean_inc_ref(x_6);
x_9 = l_Lean_Environment_contains(x_6, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_privateToUserName(x_2);
x_11 = l_Lean_Environment_contains(x_6, x_10, x_8);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_14 = lean_box(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__2___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_15; 
x_7 = lean_ctor_get(x_5, 1);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_8 = x_5;
x_9 = x_15;
goto block_14;
}
else
{
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_10);
x_11 = x_8;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_7);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_45; 
x_17 = lean_ctor_get(x_6, 0);
x_45 = !lean_is_exclusive(x_6);
if (x_45 == 0)
{
x_18 = x_6;
x_19 = x_45;
goto block_44;
}
else
{
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_box(0);
x_19 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_30; 
lean_del_object(x_18);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_dec_ref(x_5);
x_22 = lean_ctor_get(x_20, 0);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
x_23 = x_20;
x_24 = x_30;
goto block_29;
}
else
{
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_22);
x_25 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_26; 
x_26 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__2___redArg(x_25, x_21);
lean_dec_ref(x_25);
return x_26;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_43; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec_ref(x_5);
x_32 = lean_ctor_get(x_20, 0);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
x_33 = x_20;
x_34 = x_43;
goto block_42;
}
else
{
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_box(0);
x_34 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_35; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_32);
x_35 = x_18;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_32);
x_35 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_36; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_35);
x_36 = x_33;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_35);
x_36 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_37; 
x_37 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__2___redArg(x_36, x_31);
lean_dec_ref(x_36);
return x_37;
}
}
}
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
x_46 = lean_ctor_get(x_5, 0);
x_47 = lean_ctor_get(x_5, 1);
x_54 = !lean_is_exclusive(x_5);
if (x_54 == 0)
{
x_48 = x_5;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_5);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_9 = lean_st_ref_get(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_6, 2);
x_12 = lean_ctor_get(x_6, 3);
x_13 = lean_ctor_get(x_6, 4);
x_14 = lean_ctor_get(x_6, 5);
x_15 = lean_ctor_get(x_6, 6);
x_16 = lean_ctor_get(x_6, 7);
x_17 = lean_ctor_get(x_6, 10);
x_18 = lean_ctor_get(x_6, 11);
x_19 = lean_st_ref_get(x_7);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc_ref(x_10);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_21, 0, x_10);
lean_inc_ref(x_10);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(x_22, 0, x_10);
lean_inc(x_16);
lean_inc(x_15);
lean_inc_ref(x_10);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(x_23, 0, x_10);
lean_closure_set(x_23, 1, x_15);
lean_closure_set(x_23, 2, x_16);
lean_inc(x_15);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(x_24, 0, x_15);
lean_inc(x_16);
lean_inc(x_15);
lean_inc_ref(x_11);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(x_25, 0, x_10);
lean_closure_set(x_25, 1, x_11);
lean_closure_set(x_25, 2, x_15);
lean_closure_set(x_25, 3, x_16);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_23);
lean_ctor_set(x_26, 4, x_25);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_18);
lean_inc(x_17);
x_27 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_17);
lean_ctor_set(x_27, 2, x_18);
lean_ctor_set(x_27, 3, x_12);
lean_ctor_set(x_27, 4, x_13);
lean_ctor_set(x_27, 5, x_14);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_apply_2(x_1, x_27, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 2);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__4___redArg(x_35, x_36, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_72; 
lean_dec_ref(x_37);
x_38 = lean_st_ref_take(x_7);
x_39 = lean_ctor_get(x_38, 0);
x_40 = lean_ctor_get(x_38, 2);
x_41 = lean_ctor_get(x_38, 3);
x_42 = lean_ctor_get(x_38, 4);
x_43 = lean_ctor_get(x_38, 5);
x_44 = lean_ctor_get(x_38, 6);
x_45 = lean_ctor_get(x_38, 7);
x_46 = lean_ctor_get(x_38, 8);
x_72 = !lean_is_exclusive(x_38);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_38, 1);
lean_dec(x_73);
x_47 = x_38;
x_48 = x_72;
goto block_71;
}
else
{
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_38);
x_47 = lean_box(0);
x_48 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_49; 
if (x_48 == 0)
{
lean_ctor_set(x_47, 1, x_33);
x_49 = x_47;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_70, 0, x_39);
lean_ctor_set(x_70, 1, x_33);
lean_ctor_set(x_70, 2, x_40);
lean_ctor_set(x_70, 3, x_41);
lean_ctor_set(x_70, 4, x_42);
lean_ctor_set(x_70, 5, x_43);
lean_ctor_set(x_70, 6, x_44);
lean_ctor_set(x_70, 7, x_45);
lean_ctor_set(x_70, 8, x_46);
x_49 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_st_ref_set(x_7, x_49);
x_51 = l_List_reverse___redArg(x_34);
x_52 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__5(x_51, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; uint8_t x_59; 
x_59 = !lean_is_exclusive(x_52);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_52, 0);
lean_dec(x_60);
x_53 = x_52;
x_54 = x_59;
goto block_58;
}
else
{
lean_dec(x_52);
x_53 = lean_box(0);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_54 == 0)
{
lean_ctor_set(x_53, 0, x_32);
x_55 = x_53;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_32);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_68; 
lean_dec(x_32);
x_61 = lean_ctor_get(x_52, 0);
x_68 = !lean_is_exclusive(x_52);
if (x_68 == 0)
{
x_62 = x_52;
x_63 = x_68;
goto block_67;
}
else
{
lean_inc(x_61);
lean_dec(x_52);
x_62 = lean_box(0);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
if (x_63 == 0)
{
x_64 = x_62;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_61);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_81; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_74 = lean_ctor_get(x_37, 0);
x_81 = !lean_is_exclusive(x_37);
if (x_81 == 0)
{
x_75 = x_37;
x_76 = x_81;
goto block_80;
}
else
{
lean_inc(x_74);
lean_dec(x_37);
x_75 = lean_box(0);
x_76 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_77; 
if (x_76 == 0)
{
x_77 = x_75;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_74);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
}
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_30, 0);
lean_inc(x_82);
lean_dec_ref(x_30);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc_ref(x_84);
lean_dec_ref(x_82);
x_85 = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___closed__0));
x_86 = lean_string_dec_eq(x_84, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_87, 0, x_84);
x_88 = l_Lean_MessageData_ofFormat(x_87);
x_89 = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6___redArg(x_83, x_88, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_83);
return x_89;
}
else
{
lean_object* x_90; 
lean_dec_ref(x_84);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_90 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg(x_83);
return x_90;
}
}
else
{
lean_object* x_91; 
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_91 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__8___redArg();
return x_91;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = ((lean_object*)(l_Lean_Elab_Term_getPatternVars___closed__0));
x_10 = lean_alloc_closure((void*)(l_Lean_expandMacros), 4, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_inc_ref(x_6);
lean_inc_ref(x_2);
x_11 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_obj_once(&l_Lean_Elab_Term_collectPatternVars___redArg___closed__0, &l_Lean_Elab_Term_collectPatternVars___redArg___closed__0_once, _init_l_Lean_Elab_Term_collectPatternVars___redArg___closed__0);
x_14 = lean_st_mk_ref(x_13);
lean_inc(x_14);
x_15 = l_Lean_Elab_Term_CollectPatternVars_collect(x_12, x_14, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; uint8_t x_24; 
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_16 = x_15;
x_17 = x_24;
goto block_23;
}
else
{
lean_dec(x_15);
x_16 = lean_box(0);
x_17 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_st_ref_get(x_14);
lean_dec(x_14);
x_19 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_19);
lean_dec(x_18);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_19);
x_20 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec(x_14);
x_26 = lean_ctor_get(x_15, 0);
x_33 = !lean_is_exclusive(x_15);
if (x_33 == 0)
{
x_27 = x_15;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_41; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_34 = lean_ctor_get(x_11, 0);
x_41 = !lean_is_exclusive(x_11);
if (x_41 == 0)
{
x_35 = x_11;
x_36 = x_41;
goto block_40;
}
else
{
lean_inc(x_34);
lean_dec(x_11);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_34);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_getPatternVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__0___redArg(x_1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__2___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__2(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__8___redArg();
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__1___redArg(x_1, x_2, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__4___redArg(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7(x_1, x_2, x_3);
lean_dec_ref(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6_spec__10___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6_spec__10(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___redArg(x_1, x_2, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__6_spec__10_spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11_spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11_spec__15___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7_spec__11_spec__15(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_getPatternsVars_spec__1___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = ((lean_object*)(l_Lean_Elab_Term_getPatternVars___lam__0___closed__1));
x_4 = lean_name_eq(x_2, x_3);
if (x_4 == 0)
{
return x_1;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_getPatternsVars_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_getPatternsVars_spec__1___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__4___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__8___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__8___redArg___closed__0);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__4___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__4___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0_spec__1___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_61; uint8_t x_62; 
x_9 = lean_st_ref_get(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*8);
lean_dec_ref(x_10);
x_12 = lean_st_ref_get(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_13);
lean_dec(x_12);
x_14 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__2);
lean_inc(x_1);
x_15 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*1 + 1, x_2);
x_16 = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
x_17 = lean_box(1);
x_18 = lean_box(0);
x_61 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_14, x_16, x_13, x_17, x_18);
x_62 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4_spec__7___redArg(x_61, x_15);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_71; lean_object* x_72; uint8_t x_85; 
x_63 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__8));
x_64 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0___redArg(x_63, x_6);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_85 = lean_unbox(x_65);
lean_dec(x_65);
if (x_85 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
x_19 = x_5;
x_20 = x_7;
goto block_60;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__15);
if (x_11 == 0)
{
lean_object* x_95; 
x_95 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__18));
x_87 = x_95;
goto block_94;
}
else
{
lean_object* x_96; 
x_96 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__19));
x_87 = x_96;
goto block_94;
}
block_94:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = l_Lean_stringToMessageData(x_87);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_obj_once(&l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__3, &l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__3_once, _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidNamedArgs___redArg___closed__3);
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
if (x_2 == 0)
{
lean_object* x_92; 
x_92 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__16));
x_71 = x_91;
x_72 = x_92;
goto block_84;
}
else
{
lean_object* x_93; 
x_93 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__17));
x_71 = x_91;
x_72 = x_93;
goto block_84;
}
}
}
block_70:
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg(x_63, x_68, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_69) == 0)
{
lean_dec_ref(x_69);
x_19 = x_5;
x_20 = x_7;
goto block_60;
}
else
{
lean_dec_ref(x_15);
return x_69;
}
}
block_84:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_73 = l_Lean_stringToMessageData(x_72);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__10);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_MessageData_ofName(x_1);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_Name_isAnonymous(x_3);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__12);
x_81 = l_Lean_MessageData_ofName(x_3);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_66 = x_78;
x_67 = x_82;
goto block_70;
}
else
{
lean_object* x_83; 
lean_dec(x_3);
x_83 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__13);
x_66 = x_78;
x_67 = x_83;
goto block_70;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec_ref(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
block_60:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_58; 
x_21 = lean_st_ref_take(x_20);
x_22 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_ctor_get(x_21, 2);
x_26 = lean_ctor_get(x_21, 3);
x_27 = lean_ctor_get(x_21, 4);
x_28 = lean_ctor_get(x_21, 6);
x_29 = lean_ctor_get(x_21, 7);
x_30 = lean_ctor_get(x_21, 8);
x_58 = !lean_is_exclusive(x_21);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_21, 5);
lean_dec(x_59);
x_31 = x_21;
x_32 = x_58;
goto block_57;
}
else
{
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_31 = lean_box(0);
x_32 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_22, 2);
lean_inc(x_33);
lean_dec_ref(x_22);
x_34 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_16, x_23, x_15, x_33, x_18);
lean_dec(x_33);
x_35 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__5);
if (x_32 == 0)
{
lean_ctor_set(x_31, 5, x_35);
lean_ctor_set(x_31, 0, x_34);
x_36 = x_31;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_56, 0, x_34);
lean_ctor_set(x_56, 1, x_24);
lean_ctor_set(x_56, 2, x_25);
lean_ctor_set(x_56, 3, x_26);
lean_ctor_set(x_56, 4, x_27);
lean_ctor_set(x_56, 5, x_35);
lean_ctor_set(x_56, 6, x_28);
lean_ctor_set(x_56, 7, x_29);
lean_ctor_set(x_56, 8, x_30);
x_36 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_53; 
x_37 = lean_st_ref_set(x_20, x_36);
x_38 = lean_st_ref_take(x_19);
x_39 = lean_ctor_get(x_38, 0);
x_40 = lean_ctor_get(x_38, 2);
x_41 = lean_ctor_get(x_38, 3);
x_42 = lean_ctor_get(x_38, 4);
x_53 = !lean_is_exclusive(x_38);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_38, 1);
lean_dec(x_54);
x_43 = x_38;
x_44 = x_53;
goto block_52;
}
else
{
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_38);
x_43 = lean_box(0);
x_44 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__4___closed__6);
if (x_44 == 0)
{
lean_ctor_set(x_43, 1, x_45);
x_46 = x_43;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_45);
lean_ctor_set(x_51, 2, x_40);
lean_ctor_set(x_51, 3, x_41);
lean_ctor_set(x_51, 4, x_42);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_st_ref_set(x_19, x_46);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0_spec__1___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_6);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_17 = l_Lean_Environment_header(x_1);
x_18 = lean_ctor_get(x_17, 3);
lean_inc_ref(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_instInhabitedEffectiveImport_default;
x_20 = lean_array_uget_borrowed(x_3, x_5);
x_21 = lean_array_get(x_19, x_18, x_20);
lean_dec_ref(x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = 0;
lean_inc(x_2);
x_25 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0_spec__1___redArg(x_23, x_24, x_2, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; size_t x_27; size_t x_28; 
lean_dec_ref(x_25);
x_26 = lean_box(0);
x_27 = 1;
x_28 = lean_usize_add(x_5, x_27);
x_5 = x_28;
x_6 = x_26;
goto _start;
}
else
{
lean_dec(x_2);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_30; 
x_11 = lean_st_ref_get(x_9);
x_15 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_15);
lean_dec(x_11);
x_30 = l_Lean_Environment_getModuleIdxFor_x3f(x_15, x_1);
if (lean_obj_tag(x_30) == 0)
{
lean_dec_ref(x_15);
lean_dec(x_1);
goto block_14;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = l_Lean_Environment_header(x_15);
x_33 = lean_ctor_get(x_32, 3);
lean_inc_ref(x_33);
lean_dec_ref(x_32);
x_34 = lean_array_get_size(x_33);
x_35 = lean_nat_dec_lt(x_31, x_34);
if (x_35 == 0)
{
lean_dec_ref(x_33);
lean_dec(x_31);
lean_dec_ref(x_15);
lean_dec(x_1);
goto block_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_st_ref_get(x_9);
x_37 = lean_ctor_get(x_36, 0);
lean_inc_ref(x_37);
lean_dec(x_36);
x_38 = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___closed__2);
x_39 = lean_array_fget(x_33, x_31);
lean_dec(x_31);
lean_dec_ref(x_33);
if (x_2 == 0)
{
lean_dec_ref(x_37);
x_40 = x_2;
goto block_51;
}
else
{
uint8_t x_52; 
lean_inc(x_1);
x_52 = l_Lean_isMarkedMeta(x_37, x_1);
if (x_52 == 0)
{
x_40 = x_2;
goto block_51;
}
else
{
uint8_t x_53; 
x_53 = 0;
x_40 = x_53;
goto block_51;
}
}
block_51:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc_ref(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
lean_inc(x_1);
x_43 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0_spec__1___redArg(x_42, x_40, x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_43);
x_44 = l_Lean_indirectModUseExt;
x_45 = lean_box(1);
x_46 = lean_box(0);
lean_inc_ref(x_15);
x_47 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_38, x_44, x_15, x_45, x_46);
x_48 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3_spec__6___redArg(x_47, x_1);
lean_dec(x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__3___closed__3));
x_16 = x_49;
goto block_29;
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec_ref(x_48);
x_16 = x_50;
goto block_29;
}
}
else
{
lean_dec_ref(x_15);
lean_dec(x_1);
return x_43;
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
block_29:
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_box(0);
x_18 = lean_array_size(x_16);
x_19 = 0;
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0_spec__2(x_15, x_1, x_16, x_18, x_19, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; uint8_t x_27; 
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_20, 0);
lean_dec(x_28);
x_21 = x_20;
x_22 = x_27;
goto block_26;
}
else
{
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_17);
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_17);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
else
{
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec_ref(x_1);
x_14 = 1;
x_15 = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0(x_12, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec_ref(x_15);
x_16 = lean_box(0);
x_1 = x_13;
x_2 = x_16;
goto _start;
}
else
{
lean_dec(x_13);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_15; 
x_7 = lean_ctor_get(x_5, 1);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_8 = x_5;
x_9 = x_15;
goto block_14;
}
else
{
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_10);
x_11 = x_8;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_7);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_45; 
x_17 = lean_ctor_get(x_6, 0);
x_45 = !lean_is_exclusive(x_6);
if (x_45 == 0)
{
x_18 = x_6;
x_19 = x_45;
goto block_44;
}
else
{
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_box(0);
x_19 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_30; 
lean_del_object(x_18);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_dec_ref(x_5);
x_22 = lean_ctor_get(x_20, 0);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
x_23 = x_20;
x_24 = x_30;
goto block_29;
}
else
{
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_22);
x_25 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_26; 
x_26 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__2___redArg(x_25, x_21);
lean_dec_ref(x_25);
return x_26;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_43; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec_ref(x_5);
x_32 = lean_ctor_get(x_20, 0);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
x_33 = x_20;
x_34 = x_43;
goto block_42;
}
else
{
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_box(0);
x_34 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_35; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_32);
x_35 = x_18;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_32);
x_35 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_36; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_35);
x_36 = x_33;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_35);
x_36 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_37; 
x_37 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__2___redArg(x_36, x_31);
lean_dec_ref(x_36);
return x_37;
}
}
}
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
x_46 = lean_ctor_get(x_5, 0);
x_47 = lean_ctor_get(x_5, 1);
x_54 = !lean_is_exclusive(x_5);
if (x_54 == 0)
{
x_48 = x_5;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_5);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__3___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0_spec__7___redArg___closed__5);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__3___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_26; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
lean_inc(x_11);
x_13 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Term_CollectPatternVars_main_spec__0___redArg(x_11, x_4);
x_14 = lean_ctor_get(x_13, 0);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
x_15 = x_13;
x_16 = x_26;
goto block_25;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_26;
goto block_25;
}
block_25:
{
uint8_t x_17; 
x_17 = lean_unbox(x_14);
lean_dec(x_14);
if (x_17 == 0)
{
lean_del_object(x_15);
lean_dec(x_12);
lean_dec(x_11);
x_1 = x_10;
goto _start;
}
else
{
lean_object* x_19; 
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 3);
lean_ctor_set(x_15, 0, x_12);
x_19 = x_15;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_12);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_MessageData_ofFormat(x_19);
x_21 = l_Lean_addTrace___at___00Lean_Elab_Term_CollectPatternVars_main_spec__1___redArg(x_11, x_20, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_21) == 0)
{
lean_dec_ref(x_21);
x_1 = x_10;
goto _start;
}
else
{
lean_dec(x_10);
return x_21;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__2___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_10 = lean_st_ref_get(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_7, 2);
x_13 = lean_ctor_get(x_7, 3);
x_14 = lean_ctor_get(x_7, 4);
x_15 = lean_ctor_get(x_7, 5);
x_16 = lean_ctor_get(x_7, 6);
x_17 = lean_ctor_get(x_7, 7);
x_18 = lean_ctor_get(x_7, 10);
x_19 = lean_ctor_get(x_7, 11);
x_20 = lean_st_ref_get(x_8);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_inc_ref(x_11);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_22, 0, x_11);
lean_inc_ref(x_11);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(x_23, 0, x_11);
lean_inc(x_17);
lean_inc(x_16);
lean_inc_ref(x_11);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(x_24, 0, x_11);
lean_closure_set(x_24, 1, x_16);
lean_closure_set(x_24, 2, x_17);
lean_inc(x_16);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(x_25, 0, x_16);
lean_inc(x_17);
lean_inc(x_16);
lean_inc_ref(x_12);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(x_26, 0, x_11);
lean_closure_set(x_26, 1, x_12);
lean_closure_set(x_26, 2, x_16);
lean_closure_set(x_26, 3, x_17);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_24);
lean_ctor_set(x_27, 4, x_26);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_19);
lean_inc(x_18);
x_28 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_18);
lean_ctor_set(x_28, 2, x_19);
lean_ctor_set(x_28, 3, x_13);
lean_ctor_set(x_28, 4, x_14);
lean_ctor_set(x_28, 5, x_15);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_apply_2(x_1, x_28, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 2);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_box(0);
x_38 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__1___redArg(x_36, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_73; 
lean_dec_ref(x_38);
x_39 = lean_st_ref_take(x_8);
x_40 = lean_ctor_get(x_39, 0);
x_41 = lean_ctor_get(x_39, 2);
x_42 = lean_ctor_get(x_39, 3);
x_43 = lean_ctor_get(x_39, 4);
x_44 = lean_ctor_get(x_39, 5);
x_45 = lean_ctor_get(x_39, 6);
x_46 = lean_ctor_get(x_39, 7);
x_47 = lean_ctor_get(x_39, 8);
x_73 = !lean_is_exclusive(x_39);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_39, 1);
lean_dec(x_74);
x_48 = x_39;
x_49 = x_73;
goto block_72;
}
else
{
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_39);
x_48 = lean_box(0);
x_49 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_50; 
if (x_49 == 0)
{
lean_ctor_set(x_48, 1, x_34);
x_50 = x_48;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_71, 0, x_40);
lean_ctor_set(x_71, 1, x_34);
lean_ctor_set(x_71, 2, x_41);
lean_ctor_set(x_71, 3, x_42);
lean_ctor_set(x_71, 4, x_43);
lean_ctor_set(x_71, 5, x_44);
lean_ctor_set(x_71, 6, x_45);
lean_ctor_set(x_71, 7, x_46);
lean_ctor_set(x_71, 8, x_47);
x_50 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_st_ref_set(x_8, x_50);
x_52 = l_List_reverse___redArg(x_35);
x_53 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__2___redArg(x_52, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; uint8_t x_60; 
x_60 = !lean_is_exclusive(x_53);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_53, 0);
lean_dec(x_61);
x_54 = x_53;
x_55 = x_60;
goto block_59;
}
else
{
lean_dec(x_53);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
lean_ctor_set(x_54, 0, x_33);
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_33);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_dec(x_33);
x_62 = lean_ctor_get(x_53, 0);
x_69 = !lean_is_exclusive(x_53);
if (x_69 == 0)
{
x_63 = x_53;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_53);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_82; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec_ref(x_7);
x_75 = lean_ctor_get(x_38, 0);
x_82 = !lean_is_exclusive(x_38);
if (x_82 == 0)
{
x_76 = x_38;
x_77 = x_82;
goto block_81;
}
else
{
lean_inc(x_75);
lean_dec(x_38);
x_76 = lean_box(0);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_77 == 0)
{
x_78 = x_76;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_75);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
}
else
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_31, 0);
lean_inc(x_83);
lean_dec_ref(x_31);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc_ref(x_85);
lean_dec_ref(x_83);
x_86 = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternVars_spec__0___redArg___closed__0));
x_87 = lean_string_dec_eq(x_85, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_88, 0, x_85);
x_89 = l_Lean_MessageData_ofFormat(x_88);
x_90 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar_spec__0___redArg(x_84, x_89, x_5, x_6, x_7, x_8);
lean_dec(x_84);
return x_90;
}
else
{
lean_object* x_91; 
lean_dec_ref(x_85);
lean_dec_ref(x_7);
x_91 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__3___redArg(x_84);
return x_91;
}
}
else
{
lean_object* x_92; 
lean_dec_ref(x_7);
x_92 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__4___redArg();
return x_92;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_getPatternsVars_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_box(x_13);
x_16 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_getPatternsVars_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_array_uget_borrowed(x_1, x_3);
lean_inc(x_17);
x_18 = lean_alloc_closure((void*)(l_Lean_expandMacros), 4, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_16);
lean_inc_ref(x_10);
x_19 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0___redArg(x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_21 = l_Lean_Elab_Term_CollectPatternVars_collect(x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; size_t x_23; size_t x_24; 
lean_dec_ref(x_21);
x_22 = lean_box(0);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_3 = x_24;
x_4 = x_22;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_26 = lean_ctor_get(x_21, 0);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
x_27 = x_21;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_41; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_34 = lean_ctor_get(x_19, 0);
x_41 = !lean_is_exclusive(x_19);
if (x_41 == 0)
{
x_35 = x_19;
x_36 = x_41;
goto block_40;
}
else
{
lean_inc(x_34);
lean_dec(x_19);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_34);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_getPatternsVars_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_getPatternsVars_spec__1(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternsVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_9 = lean_obj_once(&l_Lean_Elab_Term_collectPatternVars___redArg___closed__0, &l_Lean_Elab_Term_collectPatternVars___redArg___closed__0_once, _init_l_Lean_Elab_Term_collectPatternVars___redArg___closed__0);
x_10 = lean_st_mk_ref(x_9);
x_15 = lean_box(0);
x_16 = lean_array_size(x_1);
x_17 = 0;
lean_inc(x_10);
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_getPatternsVars_spec__1(x_1, x_16, x_17, x_15, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_dec_ref(x_18);
goto block_14;
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec_ref(x_18);
goto block_14;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_10);
x_19 = lean_ctor_get(x_18, 0);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
x_20 = x_18;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
block_14:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_st_ref_get(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternsVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_getPatternsVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__3___redArg(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__4___redArg();
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__1___redArg(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__2___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0_spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
x_13 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_getPatternsVars_spec__0_spec__0_spec__1(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_getPatternVarNames_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Syntax_getId(x_5);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_getPatternVarNames_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_getPatternVarNames_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternVarNames(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_getPatternVarNames_spec__0(x_2, x_3, x_1);
return x_4;
}
}
lean_object* runtime_initialize_Lean_Elab_Arg(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_MatchAltView(uint8_t builtin);
lean_object* runtime_initialize_Init_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PatternVar(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Arg(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_MatchAltView(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Syntax(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_CollectPatternVars_instInhabitedState_default = _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedState_default();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_instInhabitedState_default);
l_Lean_Elab_Term_CollectPatternVars_instInhabitedState = _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedState();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_instInhabitedState);
l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default = _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext_default);
l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext = _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PatternVar(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Arg(uint8_t builtin);
lean_object* initialize_Lean_Elab_MatchAltView(uint8_t builtin);
lean_object* initialize_Init_Syntax(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PatternVar(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Arg(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_MatchAltView(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Syntax(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PatternVar(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PatternVar(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PatternVar(builtin);
}
#ifdef __cplusplus
}
#endif
