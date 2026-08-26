// Lean compiler output
// Module: Lean.Meta.DecLevel
// Imports: public import Lean.Meta.InferType
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
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLevelMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t l_Lean_instHashableLevelMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_normalizeLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_LMVarId_isReadOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMVar(lean_object*);
lean_object* l_Lean_MessageData_ofLevel(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "isLevelDefEq"};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "step"};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(198, 68, 1, 201, 101, 121, 53, 108)}};
static const lean_ctor_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 1, 100, 166, 77, 133, 145, 204)}};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6;
static const lean_string_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "decAux\?, "};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8;
static const lean_string_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10;
static const lean_string_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Meta.DecLevel"};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__11_value;
static const lean_string_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "_private.Lean.Meta.DecLevel.0.Lean.Meta.decAux\?"};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__12_value;
static const lean_string_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_decLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "invalid universe level, "};
static const lean_object* l_Lean_Meta_decLevel___closed__0 = (const lean_object*)&l_Lean_Meta_decLevel___closed__0_value;
static lean_once_cell_t l_Lean_Meta_decLevel___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_decLevel___closed__1;
static const lean_string_object l_Lean_Meta_decLevel___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = " is not greater than 0"};
static const lean_object* l_Lean_Meta_decLevel___closed__2 = (const lean_object*)&l_Lean_Meta_decLevel___closed__2_value;
static lean_once_cell_t l_Lean_Meta_decLevel___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_decLevel___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DecLevel"};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(85, 216, 73, 246, 80, 140, 232, 208)}};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(192, 180, 156, 108, 19, 54, 121, 237)}};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(249, 156, 0, 74, 190, 195, 155, 79)}};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 200, 104, 203, 2, 195, 91, 0)}};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(240, 125, 94, 183, 99, 131, 38, 240)}};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(241, 130, 41, 175, 161, 97, 225, 244)}};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(180, 50, 221, 62, 163, 161, 147, 163)}};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(104, 244, 58, 8, 64, 131, 252, 250)}};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(131, 168, 38, 102, 16, 73, 117, 166)}};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3(lean_object* v_msg_2_, uint8_t v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___f_9_; lean_object* v___f_10_; lean_object* v___x_6922__overap_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___f_9_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3___closed__0));
v___f_10_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_10_, 0, v___f_9_);
v___x_6922__overap_11_ = lean_panic_fn_borrowed(v___f_10_, v_msg_2_);
lean_dec_ref(v___f_10_);
v___x_12_ = lean_box(v___y_3_);
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_5_);
lean_inc_ref(v___y_4_);
v___x_13_ = lean_apply_6(v___x_6922__overap_11_, v___x_12_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3___boxed(lean_object* v_msg_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_){
_start:
{
uint8_t v___y_7787__boxed_21_; lean_object* v_res_22_; 
v___y_7787__boxed_21_ = lean_unbox(v___y_15_);
v_res_22_ = l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3(v_msg_14_, v___y_7787__boxed_21_, v___y_16_, v___y_17_, v___y_18_, v___y_19_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4(lean_object* v_msgData_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v___x_29_; lean_object* v_env_30_; lean_object* v___x_31_; lean_object* v_mctx_32_; lean_object* v_lctx_33_; lean_object* v_options_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_29_ = lean_st_ref_get(v___y_27_);
v_env_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc_ref(v_env_30_);
lean_dec(v___x_29_);
v___x_31_ = lean_st_ref_get(v___y_25_);
v_mctx_32_ = lean_ctor_get(v___x_31_, 0);
lean_inc_ref(v_mctx_32_);
lean_dec(v___x_31_);
v_lctx_33_ = lean_ctor_get(v___y_24_, 2);
v_options_34_ = lean_ctor_get(v___y_26_, 2);
lean_inc_ref(v_options_34_);
lean_inc_ref(v_lctx_33_);
v___x_35_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_35_, 0, v_env_30_);
lean_ctor_set(v___x_35_, 1, v_mctx_32_);
lean_ctor_set(v___x_35_, 2, v_lctx_33_);
lean_ctor_set(v___x_35_, 3, v_options_34_);
v___x_36_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v_msgData_23_);
v___x_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4___boxed(lean_object* v_msgData_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4(v_msgData_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec(v___y_40_);
lean_dec_ref(v___y_39_);
return v_res_44_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_45_; double v___x_46_; 
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_float_of_nat(v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg(lean_object* v_cls_50_, lean_object* v_msg_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_ref_57_; lean_object* v___x_58_; lean_object* v_a_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_103_; 
v_ref_57_ = lean_ctor_get(v___y_54_, 5);
v___x_58_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4(v_msg_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
v_a_59_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_103_ == 0)
{
v___x_61_ = v___x_58_;
v_isShared_62_ = v_isSharedCheck_103_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_a_59_);
lean_dec(v___x_58_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_103_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_63_; lean_object* v_traceState_64_; lean_object* v_env_65_; lean_object* v_nextMacroScope_66_; lean_object* v_ngen_67_; lean_object* v_auxDeclNGen_68_; lean_object* v_cache_69_; lean_object* v_messages_70_; lean_object* v_infoState_71_; lean_object* v_snapshotTasks_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_102_; 
v___x_63_ = lean_st_ref_take(v___y_55_);
v_traceState_64_ = lean_ctor_get(v___x_63_, 4);
v_env_65_ = lean_ctor_get(v___x_63_, 0);
v_nextMacroScope_66_ = lean_ctor_get(v___x_63_, 1);
v_ngen_67_ = lean_ctor_get(v___x_63_, 2);
v_auxDeclNGen_68_ = lean_ctor_get(v___x_63_, 3);
v_cache_69_ = lean_ctor_get(v___x_63_, 5);
v_messages_70_ = lean_ctor_get(v___x_63_, 6);
v_infoState_71_ = lean_ctor_get(v___x_63_, 7);
v_snapshotTasks_72_ = lean_ctor_get(v___x_63_, 8);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_102_ == 0)
{
v___x_74_ = v___x_63_;
v_isShared_75_ = v_isSharedCheck_102_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_snapshotTasks_72_);
lean_inc(v_infoState_71_);
lean_inc(v_messages_70_);
lean_inc(v_cache_69_);
lean_inc(v_traceState_64_);
lean_inc(v_auxDeclNGen_68_);
lean_inc(v_ngen_67_);
lean_inc(v_nextMacroScope_66_);
lean_inc(v_env_65_);
lean_dec(v___x_63_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_102_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
uint64_t v_tid_76_; lean_object* v_traces_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_101_; 
v_tid_76_ = lean_ctor_get_uint64(v_traceState_64_, sizeof(void*)*1);
v_traces_77_ = lean_ctor_get(v_traceState_64_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v_traceState_64_);
if (v_isSharedCheck_101_ == 0)
{
v___x_79_ = v_traceState_64_;
v_isShared_80_ = v_isSharedCheck_101_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_traces_77_);
lean_dec(v_traceState_64_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_101_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; double v___x_82_; uint8_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_91_; 
v___x_81_ = lean_box(0);
v___x_82_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__0);
v___x_83_ = 0;
v___x_84_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__1));
v___x_85_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_85_, 0, v_cls_50_);
lean_ctor_set(v___x_85_, 1, v___x_81_);
lean_ctor_set(v___x_85_, 2, v___x_84_);
lean_ctor_set_float(v___x_85_, sizeof(void*)*3, v___x_82_);
lean_ctor_set_float(v___x_85_, sizeof(void*)*3 + 8, v___x_82_);
lean_ctor_set_uint8(v___x_85_, sizeof(void*)*3 + 16, v___x_83_);
v___x_86_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__2));
v___x_87_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_87_, 0, v___x_85_);
lean_ctor_set(v___x_87_, 1, v_a_59_);
lean_ctor_set(v___x_87_, 2, v___x_86_);
lean_inc(v_ref_57_);
v___x_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_88_, 0, v_ref_57_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = l_Lean_PersistentArray_push___redArg(v_traces_77_, v___x_88_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_89_);
v___x_91_ = v___x_79_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_89_);
lean_ctor_set_uint64(v_reuseFailAlloc_100_, sizeof(void*)*1, v_tid_76_);
v___x_91_ = v_reuseFailAlloc_100_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
lean_object* v___x_93_; 
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 4, v___x_91_);
v___x_93_ = v___x_74_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_env_65_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_nextMacroScope_66_);
lean_ctor_set(v_reuseFailAlloc_99_, 2, v_ngen_67_);
lean_ctor_set(v_reuseFailAlloc_99_, 3, v_auxDeclNGen_68_);
lean_ctor_set(v_reuseFailAlloc_99_, 4, v___x_91_);
lean_ctor_set(v_reuseFailAlloc_99_, 5, v_cache_69_);
lean_ctor_set(v_reuseFailAlloc_99_, 6, v_messages_70_);
lean_ctor_set(v_reuseFailAlloc_99_, 7, v_infoState_71_);
lean_ctor_set(v_reuseFailAlloc_99_, 8, v_snapshotTasks_72_);
v___x_93_ = v_reuseFailAlloc_99_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_97_; 
v___x_94_ = lean_st_ref_put(v___y_55_, v___x_93_);
v___x_95_ = lean_box(0);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 0, v___x_95_);
v___x_97_ = v___x_61_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_95_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___boxed(lean_object* v_cls_104_, lean_object* v_msg_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg(v_cls_104_, v_msg_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8_spec__9___redArg(lean_object* v_x_112_, lean_object* v_x_113_, lean_object* v_x_114_, lean_object* v_x_115_){
_start:
{
lean_object* v_ks_116_; lean_object* v_vs_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_141_; 
v_ks_116_ = lean_ctor_get(v_x_112_, 0);
v_vs_117_ = lean_ctor_get(v_x_112_, 1);
v_isSharedCheck_141_ = !lean_is_exclusive(v_x_112_);
if (v_isSharedCheck_141_ == 0)
{
v___x_119_ = v_x_112_;
v_isShared_120_ = v_isSharedCheck_141_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_vs_117_);
lean_inc(v_ks_116_);
lean_dec(v_x_112_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_141_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_array_get_size(v_ks_116_);
v___x_122_ = lean_nat_dec_lt(v_x_113_, v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_126_; 
lean_dec(v_x_113_);
v___x_123_ = lean_array_push(v_ks_116_, v_x_114_);
v___x_124_ = lean_array_push(v_vs_117_, v_x_115_);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 1, v___x_124_);
lean_ctor_set(v___x_119_, 0, v___x_123_);
v___x_126_ = v___x_119_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v___x_124_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
else
{
lean_object* v_k_x27_128_; uint8_t v___x_129_; 
v_k_x27_128_ = lean_array_fget_borrowed(v_ks_116_, v_x_113_);
v___x_129_ = l_Lean_instBEqLevelMVarId_beq(v_x_114_, v_k_x27_128_);
if (v___x_129_ == 0)
{
lean_object* v___x_131_; 
if (v_isShared_120_ == 0)
{
v___x_131_ = v___x_119_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_ks_116_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_vs_117_);
v___x_131_ = v_reuseFailAlloc_135_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_unsigned_to_nat(1u);
v___x_133_ = lean_nat_add(v_x_113_, v___x_132_);
lean_dec(v_x_113_);
v_x_112_ = v___x_131_;
v_x_113_ = v___x_133_;
goto _start;
}
}
else
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_136_ = lean_array_fset(v_ks_116_, v_x_113_, v_x_114_);
v___x_137_ = lean_array_fset(v_vs_117_, v_x_113_, v_x_115_);
lean_dec(v_x_113_);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 1, v___x_137_);
lean_ctor_set(v___x_119_, 0, v___x_136_);
v___x_139_ = v___x_119_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v___x_137_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_n_142_, lean_object* v_k_143_, lean_object* v_v_144_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_unsigned_to_nat(0u);
v___x_146_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8_spec__9___redArg(v_n_142_, v___x_145_, v_k_143_, v_v_144_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(lean_object* v_x_148_, size_t v_x_149_, size_t v_x_150_, lean_object* v_x_151_, lean_object* v_x_152_){
_start:
{
if (lean_obj_tag(v_x_148_) == 0)
{
lean_object* v_es_153_; size_t v___x_154_; size_t v___x_155_; lean_object* v_j_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v_es_153_ = lean_ctor_get(v_x_148_, 0);
v___x_154_ = ((size_t)31ULL);
v___x_155_ = lean_usize_land(v_x_149_, v___x_154_);
v_j_156_ = lean_usize_to_nat(v___x_155_);
v___x_157_ = lean_array_get_size(v_es_153_);
v___x_158_ = lean_nat_dec_lt(v_j_156_, v___x_157_);
if (v___x_158_ == 0)
{
lean_dec(v_j_156_);
lean_dec(v_x_152_);
lean_dec(v_x_151_);
return v_x_148_;
}
else
{
lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_197_; 
lean_inc_ref(v_es_153_);
v_isSharedCheck_197_ = !lean_is_exclusive(v_x_148_);
if (v_isSharedCheck_197_ == 0)
{
lean_object* v_unused_198_; 
v_unused_198_ = lean_ctor_get(v_x_148_, 0);
lean_dec(v_unused_198_);
v___x_160_ = v_x_148_;
v_isShared_161_ = v_isSharedCheck_197_;
goto v_resetjp_159_;
}
else
{
lean_dec(v_x_148_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_197_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v_v_162_; lean_object* v___x_163_; lean_object* v_xs_x27_164_; lean_object* v___y_166_; 
v_v_162_ = lean_array_fget(v_es_153_, v_j_156_);
v___x_163_ = lean_box(0);
v_xs_x27_164_ = lean_array_fset(v_es_153_, v_j_156_, v___x_163_);
switch(lean_obj_tag(v_v_162_))
{
case 0:
{
lean_object* v_key_171_; lean_object* v_val_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_182_; 
v_key_171_ = lean_ctor_get(v_v_162_, 0);
v_val_172_ = lean_ctor_get(v_v_162_, 1);
v_isSharedCheck_182_ = !lean_is_exclusive(v_v_162_);
if (v_isSharedCheck_182_ == 0)
{
v___x_174_ = v_v_162_;
v_isShared_175_ = v_isSharedCheck_182_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_val_172_);
lean_inc(v_key_171_);
lean_dec(v_v_162_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_182_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
uint8_t v___x_176_; 
v___x_176_ = l_Lean_instBEqLevelMVarId_beq(v_x_151_, v_key_171_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; lean_object* v___x_178_; 
lean_del_object(v___x_174_);
v___x_177_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_171_, v_val_172_, v_x_151_, v_x_152_);
v___x_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
v___y_166_ = v___x_178_;
goto v___jp_165_;
}
else
{
lean_object* v___x_180_; 
lean_dec(v_val_172_);
lean_dec(v_key_171_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 1, v_x_152_);
lean_ctor_set(v___x_174_, 0, v_x_151_);
v___x_180_ = v___x_174_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_x_151_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_x_152_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
v___y_166_ = v___x_180_;
goto v___jp_165_;
}
}
}
}
case 1:
{
lean_object* v_node_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_195_; 
v_node_183_ = lean_ctor_get(v_v_162_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v_v_162_);
if (v_isSharedCheck_195_ == 0)
{
v___x_185_ = v_v_162_;
v_isShared_186_ = v_isSharedCheck_195_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_node_183_);
lean_dec(v_v_162_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_195_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
size_t v___x_187_; size_t v___x_188_; size_t v___x_189_; size_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_187_ = ((size_t)5ULL);
v___x_188_ = lean_usize_shift_right(v_x_149_, v___x_187_);
v___x_189_ = ((size_t)1ULL);
v___x_190_ = lean_usize_add(v_x_150_, v___x_189_);
v___x_191_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_node_183_, v___x_188_, v___x_190_, v_x_151_, v_x_152_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_191_);
v___x_193_ = v___x_185_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
v___y_166_ = v___x_193_;
goto v___jp_165_;
}
}
}
default: 
{
lean_object* v___x_196_; 
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v_x_151_);
lean_ctor_set(v___x_196_, 1, v_x_152_);
v___y_166_ = v___x_196_;
goto v___jp_165_;
}
}
v___jp_165_:
{
lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_167_ = lean_array_fset(v_xs_x27_164_, v_j_156_, v___y_166_);
lean_dec(v_j_156_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 0, v___x_167_);
v___x_169_ = v___x_160_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_167_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
}
else
{
lean_object* v_ks_199_; lean_object* v_vs_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_218_; 
v_ks_199_ = lean_ctor_get(v_x_148_, 0);
v_vs_200_ = lean_ctor_get(v_x_148_, 1);
v_isSharedCheck_218_ = !lean_is_exclusive(v_x_148_);
if (v_isSharedCheck_218_ == 0)
{
v___x_202_ = v_x_148_;
v_isShared_203_ = v_isSharedCheck_218_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_vs_200_);
lean_inc(v_ks_199_);
lean_dec(v_x_148_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_218_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_ks_199_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_vs_200_);
v___x_205_ = v_reuseFailAlloc_217_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v_newNode_206_; size_t v___x_207_; uint8_t v___x_208_; 
v_newNode_206_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8___redArg(v___x_205_, v_x_151_, v_x_152_);
v___x_207_ = ((size_t)7ULL);
v___x_208_ = lean_usize_dec_le(v___x_207_, v_x_150_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_209_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_206_);
v___x_210_ = lean_unsigned_to_nat(4u);
v___x_211_ = lean_nat_dec_lt(v___x_209_, v___x_210_);
lean_dec(v___x_209_);
if (v___x_211_ == 0)
{
lean_object* v_ks_212_; lean_object* v_vs_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_ks_212_ = lean_ctor_get(v_newNode_206_, 0);
lean_inc_ref(v_ks_212_);
v_vs_213_ = lean_ctor_get(v_newNode_206_, 1);
lean_inc_ref(v_vs_213_);
lean_dec_ref(v_newNode_206_);
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_216_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(v_x_150_, v_ks_212_, v_vs_213_, v___x_214_, v___x_215_);
lean_dec_ref(v_vs_213_);
lean_dec_ref(v_ks_212_);
return v___x_216_;
}
else
{
return v_newNode_206_;
}
}
else
{
return v_newNode_206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(size_t v_depth_219_, lean_object* v_keys_220_, lean_object* v_vals_221_, lean_object* v_i_222_, lean_object* v_entries_223_){
_start:
{
lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_224_ = lean_array_get_size(v_keys_220_);
v___x_225_ = lean_nat_dec_lt(v_i_222_, v___x_224_);
if (v___x_225_ == 0)
{
lean_dec(v_i_222_);
return v_entries_223_;
}
else
{
lean_object* v_k_226_; lean_object* v_v_227_; uint64_t v___x_228_; size_t v_h_229_; size_t v___x_230_; lean_object* v___x_231_; size_t v___x_232_; size_t v___x_233_; size_t v___x_234_; size_t v_h_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v_k_226_ = lean_array_fget_borrowed(v_keys_220_, v_i_222_);
v_v_227_ = lean_array_fget_borrowed(v_vals_221_, v_i_222_);
v___x_228_ = l_Lean_instHashableLevelMVarId_hash(v_k_226_);
v_h_229_ = lean_uint64_to_usize(v___x_228_);
v___x_230_ = ((size_t)5ULL);
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = ((size_t)1ULL);
v___x_233_ = lean_usize_sub(v_depth_219_, v___x_232_);
v___x_234_ = lean_usize_mul(v___x_230_, v___x_233_);
v_h_235_ = lean_usize_shift_right(v_h_229_, v___x_234_);
v___x_236_ = lean_nat_add(v_i_222_, v___x_231_);
lean_dec(v_i_222_);
lean_inc(v_v_227_);
lean_inc(v_k_226_);
v___x_237_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_entries_223_, v_h_235_, v_depth_219_, v_k_226_, v_v_227_);
v_i_222_ = v___x_236_;
v_entries_223_ = v___x_237_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_depth_239_, lean_object* v_keys_240_, lean_object* v_vals_241_, lean_object* v_i_242_, lean_object* v_entries_243_){
_start:
{
size_t v_depth_boxed_244_; lean_object* v_res_245_; 
v_depth_boxed_244_ = lean_unbox_usize(v_depth_239_);
lean_dec(v_depth_239_);
v_res_245_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(v_depth_boxed_244_, v_keys_240_, v_vals_241_, v_i_242_, v_entries_243_);
lean_dec_ref(v_vals_241_);
lean_dec_ref(v_keys_240_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_x_246_, lean_object* v_x_247_, lean_object* v_x_248_, lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
size_t v_x_8017__boxed_251_; size_t v_x_8018__boxed_252_; lean_object* v_res_253_; 
v_x_8017__boxed_251_ = lean_unbox_usize(v_x_247_);
lean_dec(v_x_247_);
v_x_8018__boxed_252_ = lean_unbox_usize(v_x_248_);
lean_dec(v_x_248_);
v_res_253_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_x_246_, v_x_8017__boxed_251_, v_x_8018__boxed_252_, v_x_249_, v_x_250_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2___redArg(lean_object* v_x_254_, lean_object* v_x_255_, lean_object* v_x_256_){
_start:
{
uint64_t v___x_257_; size_t v___x_258_; size_t v___x_259_; lean_object* v___x_260_; 
v___x_257_ = l_Lean_instHashableLevelMVarId_hash(v_x_255_);
v___x_258_ = lean_uint64_to_usize(v___x_257_);
v___x_259_ = ((size_t)1ULL);
v___x_260_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_x_254_, v___x_258_, v___x_259_, v_x_255_, v_x_256_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(lean_object* v_mvarId_261_, lean_object* v_val_262_, lean_object* v___y_263_){
_start:
{
lean_object* v___x_265_; lean_object* v_mctx_266_; lean_object* v_cache_267_; lean_object* v_zetaDeltaFVarIds_268_; lean_object* v_postponed_269_; lean_object* v_diag_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_299_; 
v___x_265_ = lean_st_ref_take(v___y_263_);
v_mctx_266_ = lean_ctor_get(v___x_265_, 0);
v_cache_267_ = lean_ctor_get(v___x_265_, 1);
v_zetaDeltaFVarIds_268_ = lean_ctor_get(v___x_265_, 2);
v_postponed_269_ = lean_ctor_get(v___x_265_, 3);
v_diag_270_ = lean_ctor_get(v___x_265_, 4);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_299_ == 0)
{
v___x_272_ = v___x_265_;
v_isShared_273_ = v_isSharedCheck_299_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_diag_270_);
lean_inc(v_postponed_269_);
lean_inc(v_zetaDeltaFVarIds_268_);
lean_inc(v_cache_267_);
lean_inc(v_mctx_266_);
lean_dec(v___x_265_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_299_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v_depth_274_; lean_object* v_levelAssignDepth_275_; lean_object* v_lmvarCounter_276_; lean_object* v_mvarCounter_277_; lean_object* v_lDecls_278_; lean_object* v_decls_279_; lean_object* v_userNames_280_; lean_object* v_lAssignment_281_; lean_object* v_eAssignment_282_; lean_object* v_dAssignment_283_; lean_object* v_instanceTypedMVars_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_298_; 
v_depth_274_ = lean_ctor_get(v_mctx_266_, 0);
v_levelAssignDepth_275_ = lean_ctor_get(v_mctx_266_, 1);
v_lmvarCounter_276_ = lean_ctor_get(v_mctx_266_, 2);
v_mvarCounter_277_ = lean_ctor_get(v_mctx_266_, 3);
v_lDecls_278_ = lean_ctor_get(v_mctx_266_, 4);
v_decls_279_ = lean_ctor_get(v_mctx_266_, 5);
v_userNames_280_ = lean_ctor_get(v_mctx_266_, 6);
v_lAssignment_281_ = lean_ctor_get(v_mctx_266_, 7);
v_eAssignment_282_ = lean_ctor_get(v_mctx_266_, 8);
v_dAssignment_283_ = lean_ctor_get(v_mctx_266_, 9);
v_instanceTypedMVars_284_ = lean_ctor_get(v_mctx_266_, 10);
v_isSharedCheck_298_ = !lean_is_exclusive(v_mctx_266_);
if (v_isSharedCheck_298_ == 0)
{
v___x_286_ = v_mctx_266_;
v_isShared_287_ = v_isSharedCheck_298_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_instanceTypedMVars_284_);
lean_inc(v_dAssignment_283_);
lean_inc(v_eAssignment_282_);
lean_inc(v_lAssignment_281_);
lean_inc(v_userNames_280_);
lean_inc(v_decls_279_);
lean_inc(v_lDecls_278_);
lean_inc(v_mvarCounter_277_);
lean_inc(v_lmvarCounter_276_);
lean_inc(v_levelAssignDepth_275_);
lean_inc(v_depth_274_);
lean_dec(v_mctx_266_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_298_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_288_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2___redArg(v_lAssignment_281_, v_mvarId_261_, v_val_262_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 7, v___x_288_);
v___x_290_ = v___x_286_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_depth_274_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_levelAssignDepth_275_);
lean_ctor_set(v_reuseFailAlloc_297_, 2, v_lmvarCounter_276_);
lean_ctor_set(v_reuseFailAlloc_297_, 3, v_mvarCounter_277_);
lean_ctor_set(v_reuseFailAlloc_297_, 4, v_lDecls_278_);
lean_ctor_set(v_reuseFailAlloc_297_, 5, v_decls_279_);
lean_ctor_set(v_reuseFailAlloc_297_, 6, v_userNames_280_);
lean_ctor_set(v_reuseFailAlloc_297_, 7, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_297_, 8, v_eAssignment_282_);
lean_ctor_set(v_reuseFailAlloc_297_, 9, v_dAssignment_283_);
lean_ctor_set(v_reuseFailAlloc_297_, 10, v_instanceTypedMVars_284_);
v___x_290_ = v_reuseFailAlloc_297_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
lean_object* v___x_292_; 
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_290_);
v___x_292_ = v___x_272_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_290_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_cache_267_);
lean_ctor_set(v_reuseFailAlloc_296_, 2, v_zetaDeltaFVarIds_268_);
lean_ctor_set(v_reuseFailAlloc_296_, 3, v_postponed_269_);
lean_ctor_set(v_reuseFailAlloc_296_, 4, v_diag_270_);
v___x_292_ = v_reuseFailAlloc_296_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = lean_st_ref_put(v___y_263_, v___x_292_);
v___x_294_ = lean_box(0);
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_300_, lean_object* v_val_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(v_mvarId_300_, v_val_301_, v___y_302_);
lean_dec(v___y_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_305_, lean_object* v_vals_306_, lean_object* v_i_307_, lean_object* v_k_308_){
_start:
{
lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_309_ = lean_array_get_size(v_keys_305_);
v___x_310_ = lean_nat_dec_lt(v_i_307_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; 
lean_dec(v_i_307_);
v___x_311_ = lean_box(0);
return v___x_311_;
}
else
{
lean_object* v_k_x27_312_; uint8_t v___x_313_; 
v_k_x27_312_ = lean_array_fget_borrowed(v_keys_305_, v_i_307_);
v___x_313_ = l_Lean_instBEqLevelMVarId_beq(v_k_308_, v_k_x27_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_unsigned_to_nat(1u);
v___x_315_ = lean_nat_add(v_i_307_, v___x_314_);
lean_dec(v_i_307_);
v_i_307_ = v___x_315_;
goto _start;
}
else
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_array_fget_borrowed(v_vals_306_, v_i_307_);
lean_dec(v_i_307_);
lean_inc(v___x_317_);
v___x_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_319_, lean_object* v_vals_320_, lean_object* v_i_321_, lean_object* v_k_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg(v_keys_319_, v_vals_320_, v_i_321_, v_k_322_);
lean_dec(v_k_322_);
lean_dec_ref(v_vals_320_);
lean_dec_ref(v_keys_319_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(lean_object* v_x_324_, size_t v_x_325_, lean_object* v_x_326_){
_start:
{
if (lean_obj_tag(v_x_324_) == 0)
{
lean_object* v_es_327_; lean_object* v___x_328_; size_t v___x_329_; size_t v___x_330_; lean_object* v_j_331_; lean_object* v___x_332_; 
v_es_327_ = lean_ctor_get(v_x_324_, 0);
v___x_328_ = lean_box(2);
v___x_329_ = ((size_t)31ULL);
v___x_330_ = lean_usize_land(v_x_325_, v___x_329_);
v_j_331_ = lean_usize_to_nat(v___x_330_);
v___x_332_ = lean_array_get_borrowed(v___x_328_, v_es_327_, v_j_331_);
lean_dec(v_j_331_);
switch(lean_obj_tag(v___x_332_))
{
case 0:
{
lean_object* v_key_333_; lean_object* v_val_334_; uint8_t v___x_335_; 
v_key_333_ = lean_ctor_get(v___x_332_, 0);
v_val_334_ = lean_ctor_get(v___x_332_, 1);
v___x_335_ = l_Lean_instBEqLevelMVarId_beq(v_x_326_, v_key_333_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; 
v___x_336_ = lean_box(0);
return v___x_336_;
}
else
{
lean_object* v___x_337_; 
lean_inc(v_val_334_);
v___x_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_337_, 0, v_val_334_);
return v___x_337_;
}
}
case 1:
{
lean_object* v_node_338_; size_t v___x_339_; size_t v___x_340_; 
v_node_338_ = lean_ctor_get(v___x_332_, 0);
v___x_339_ = ((size_t)5ULL);
v___x_340_ = lean_usize_shift_right(v_x_325_, v___x_339_);
v_x_324_ = v_node_338_;
v_x_325_ = v___x_340_;
goto _start;
}
default: 
{
lean_object* v___x_342_; 
v___x_342_ = lean_box(0);
return v___x_342_;
}
}
}
else
{
lean_object* v_ks_343_; lean_object* v_vs_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_ks_343_ = lean_ctor_get(v_x_324_, 0);
v_vs_344_ = lean_ctor_get(v_x_324_, 1);
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg(v_ks_343_, v_vs_344_, v___x_345_, v_x_326_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
size_t v_x_8245__boxed_350_; lean_object* v_res_351_; 
v_x_8245__boxed_350_ = lean_unbox_usize(v_x_348_);
lean_dec(v_x_348_);
v_res_351_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(v_x_347_, v_x_8245__boxed_350_, v_x_349_);
lean_dec(v_x_349_);
lean_dec_ref(v_x_347_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg(lean_object* v_x_352_, lean_object* v_x_353_){
_start:
{
uint64_t v___x_354_; size_t v___x_355_; lean_object* v___x_356_; 
v___x_354_ = l_Lean_instHashableLevelMVarId_hash(v_x_353_);
v___x_355_ = lean_uint64_to_usize(v___x_354_);
v___x_356_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(v_x_352_, v___x_355_, v_x_353_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg___boxed(lean_object* v_x_357_, lean_object* v_x_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg(v_x_357_, v_x_358_);
lean_dec(v_x_358_);
lean_dec_ref(v_x_357_);
return v_res_359_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_370_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3));
v___x_371_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__5));
v___x_372_ = l_Lean_Name_append(v___x_371_, v___x_370_);
return v___x_372_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__7));
v___x_375_ = l_Lean_stringToMessageData(v___x_374_);
return v___x_375_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__9));
v___x_378_ = l_Lean_stringToMessageData(v___x_377_);
return v___x_378_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_382_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__13));
v___x_383_ = lean_unsigned_to_nat(24u);
v___x_384_ = lean_unsigned_to_nat(55u);
v___x_385_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__12));
v___x_386_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__11));
v___x_387_ = l_mkPanicMessageWithDecl(v___x_386_, v___x_385_, v___x_384_, v___x_383_, v___x_382_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(lean_object* v_x_388_, uint8_t v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v_u_399_; lean_object* v_v_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; 
switch(lean_obj_tag(v_x_388_))
{
case 0:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_box(0);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
return v___x_428_;
}
case 4:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec_ref_known(v_x_388_, 1);
v___x_429_ = lean_box(0);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
case 5:
{
lean_object* v_a_431_; lean_object* v___x_432_; lean_object* v_mctx_433_; lean_object* v_lAssignment_434_; lean_object* v___x_435_; 
v_a_431_ = lean_ctor_get(v_x_388_, 0);
lean_inc(v_a_431_);
lean_dec_ref_known(v_x_388_, 1);
v___x_432_ = lean_st_ref_get(v_a_391_);
v_mctx_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc_ref(v_mctx_433_);
lean_dec(v___x_432_);
v_lAssignment_434_ = lean_ctor_get(v_mctx_433_, 7);
lean_inc_ref(v_lAssignment_434_);
lean_dec_ref(v_mctx_433_);
v___x_435_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg(v_lAssignment_434_, v_a_431_);
lean_dec_ref(v_lAssignment_434_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v___x_436_; 
lean_inc(v_a_431_);
v___x_436_ = l_Lean_LMVarId_isReadOnly(v_a_431_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_507_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_507_ == 0)
{
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_507_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_507_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
uint8_t v___x_441_; 
v___x_441_ = lean_unbox(v_a_437_);
lean_dec(v_a_437_);
if (v___x_441_ == 0)
{
if (v_a_389_ == 0)
{
lean_object* v___x_443_; 
lean_dec(v_a_431_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_435_);
v___x_443_ = v___x_439_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_435_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
else
{
lean_object* v___x_445_; 
lean_del_object(v___x_439_);
v___x_445_ = l_Lean_Meta_mkFreshLevelMVar(v_a_390_, v_a_391_, v_a_392_, v_a_393_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; uint8_t v___y_448_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v_options_472_; uint8_t v_hasTrace_473_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_446_);
lean_dec_ref_known(v___x_445_, 1);
v_options_472_ = lean_ctor_get(v_a_392_, 2);
v_hasTrace_473_ = lean_ctor_get_uint8(v_options_472_, sizeof(void*)*1);
if (v_hasTrace_473_ == 0)
{
v___y_448_ = v_a_389_;
v___y_449_ = v_a_390_;
v___y_450_ = v_a_391_;
v___y_451_ = v_a_392_;
v___y_452_ = v_a_393_;
goto v___jp_447_;
}
else
{
lean_object* v_inheritedTraceOptions_474_; lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v_inheritedTraceOptions_474_ = lean_ctor_get(v_a_392_, 13);
v___x_475_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3));
v___x_476_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6_once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6);
v___x_477_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_474_, v_options_472_, v___x_476_);
if (v___x_477_ == 0)
{
v___y_448_ = v_a_389_;
v___y_449_ = v_a_390_;
v___y_450_ = v_a_391_;
v___y_451_ = v_a_392_;
v___y_452_ = v_a_393_;
goto v___jp_447_;
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_478_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8_once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8);
lean_inc(v_a_431_);
v___x_479_ = l_Lean_mkLevelMVar(v_a_431_);
v___x_480_ = l_Lean_MessageData_ofLevel(v___x_479_);
v___x_481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_478_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
v___x_482_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10_once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10);
v___x_483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_481_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
lean_inc(v_a_446_);
v___x_484_ = l_Lean_Level_succ___override(v_a_446_);
v___x_485_ = l_Lean_MessageData_ofLevel(v___x_484_);
v___x_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_483_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg(v___x_475_, v___x_486_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_dec_ref_known(v___x_487_, 1);
v___y_448_ = v_a_389_;
v___y_449_ = v_a_390_;
v___y_450_ = v_a_391_;
v___y_451_ = v_a_392_;
v___y_452_ = v_a_393_;
goto v___jp_447_;
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec(v_a_446_);
lean_dec(v_a_431_);
v_a_488_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
v___jp_447_:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
lean_inc(v_a_446_);
v___x_453_ = l_Lean_Level_succ___override(v_a_446_);
v___x_454_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(v_a_431_, v___x_453_, v___y_450_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_462_; 
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_462_ == 0)
{
lean_object* v_unused_463_; 
v_unused_463_ = lean_ctor_get(v___x_454_, 0);
lean_dec(v_unused_463_);
v___x_456_ = v___x_454_;
v_isShared_457_ = v_isSharedCheck_462_;
goto v_resetjp_455_;
}
else
{
lean_dec(v___x_454_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_462_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v_a_446_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_458_);
v___x_460_ = v___x_456_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec(v_a_446_);
v_a_464_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_454_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_454_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec(v_a_431_);
v_a_496_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_445_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_445_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
else
{
lean_object* v___x_505_; 
lean_dec(v_a_431_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_435_);
v___x_505_ = v___x_439_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_435_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec(v_a_431_);
v_a_508_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_436_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_436_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
else
{
lean_object* v_val_516_; 
lean_dec(v_a_431_);
v_val_516_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_val_516_);
lean_dec_ref_known(v___x_435_, 1);
v_x_388_ = v_val_516_;
goto _start;
}
}
case 1:
{
lean_object* v_a_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_a_518_ = lean_ctor_get(v_x_388_, 0);
lean_inc(v_a_518_);
lean_dec_ref_known(v_x_388_, 1);
v___x_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_519_, 0, v_a_518_);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
default: 
{
switch(lean_obj_tag(v_x_388_))
{
case 2:
{
lean_object* v_a_521_; lean_object* v_a_522_; 
v_a_521_ = lean_ctor_get(v_x_388_, 0);
lean_inc(v_a_521_);
v_a_522_ = lean_ctor_get(v_x_388_, 1);
lean_inc(v_a_522_);
lean_dec_ref_known(v_x_388_, 2);
v_u_399_ = v_a_521_;
v_v_400_ = v_a_522_;
v___y_401_ = v_a_390_;
v___y_402_ = v_a_391_;
v___y_403_ = v_a_392_;
v___y_404_ = v_a_393_;
goto v___jp_398_;
}
case 3:
{
lean_object* v_a_523_; lean_object* v_a_524_; 
v_a_523_ = lean_ctor_get(v_x_388_, 0);
lean_inc(v_a_523_);
v_a_524_ = lean_ctor_get(v_x_388_, 1);
lean_inc(v_a_524_);
lean_dec_ref_known(v_x_388_, 2);
v_u_399_ = v_a_523_;
v_v_400_ = v_a_524_;
v___y_401_ = v_a_390_;
v___y_402_ = v_a_391_;
v___y_403_ = v_a_392_;
v___y_404_ = v_a_393_;
goto v___jp_398_;
}
default: 
{
lean_object* v___x_525_; lean_object* v___x_526_; 
lean_dec(v_x_388_);
v___x_525_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14_once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14);
v___x_526_ = l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3(v___x_525_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
return v___x_526_;
}
}
}
}
v___jp_395_:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_box(0);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
v___jp_398_:
{
uint8_t v___x_405_; lean_object* v___x_406_; 
v___x_405_ = 0;
v___x_406_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(v_u_399_, v___x_405_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v___x_406_, 1);
if (lean_obj_tag(v_a_407_) == 0)
{
lean_dec(v_v_400_);
goto v___jp_395_;
}
else
{
lean_object* v_val_408_; lean_object* v___x_409_; 
v_val_408_ = lean_ctor_get(v_a_407_, 0);
lean_inc(v_val_408_);
lean_dec_ref_known(v_a_407_, 1);
v___x_409_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(v_v_400_, v___x_405_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_426_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_426_ == 0)
{
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_426_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_426_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
if (lean_obj_tag(v_a_410_) == 0)
{
lean_del_object(v___x_412_);
lean_dec(v_val_408_);
goto v___jp_395_;
}
else
{
lean_object* v_val_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_425_; 
v_val_414_ = lean_ctor_get(v_a_410_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v_a_410_);
if (v_isSharedCheck_425_ == 0)
{
v___x_416_ = v_a_410_;
v_isShared_417_ = v_isSharedCheck_425_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_val_414_);
lean_dec(v_a_410_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_425_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_418_ = l_Lean_mkLevelMax_x27(v_val_408_, v_val_414_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_418_);
v___x_420_ = v___x_416_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_424_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
lean_object* v___x_422_; 
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_420_);
v___x_422_ = v___x_412_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_420_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
}
}
else
{
lean_dec(v_val_408_);
return v___x_409_;
}
}
}
else
{
lean_dec(v_v_400_);
return v___x_406_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___boxed(lean_object* v_x_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
uint8_t v_a_boxed_534_; lean_object* v_res_535_; 
v_a_boxed_534_ = lean_unbox(v_a_528_);
v_res_535_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(v_x_527_, v_a_boxed_534_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0(lean_object* v_00_u03b2_536_, lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg(v_x_537_, v_x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___boxed(lean_object* v_00_u03b2_540_, lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0(v_00_u03b2_540_, v_x_541_, v_x_542_);
lean_dec(v_x_542_);
lean_dec_ref(v_x_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1(lean_object* v_mvarId_544_, lean_object* v_val_545_, uint8_t v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(v_mvarId_544_, v_val_545_, v___y_548_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___boxed(lean_object* v_mvarId_553_, lean_object* v_val_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
uint8_t v___y_8656__boxed_561_; lean_object* v_res_562_; 
v___y_8656__boxed_561_ = lean_unbox(v___y_555_);
v_res_562_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1(v_mvarId_553_, v_val_554_, v___y_8656__boxed_561_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2(lean_object* v_cls_563_, lean_object* v_msg_564_, uint8_t v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg(v_cls_563_, v_msg_564_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___boxed(lean_object* v_cls_572_, lean_object* v_msg_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
uint8_t v___y_8676__boxed_580_; lean_object* v_res_581_; 
v___y_8676__boxed_580_ = lean_unbox(v___y_574_);
v_res_581_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2(v_cls_572_, v_msg_573_, v___y_8676__boxed_580_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0(lean_object* v_00_u03b2_582_, lean_object* v_x_583_, size_t v_x_584_, lean_object* v_x_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(v_x_583_, v_x_584_, v_x_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_587_, lean_object* v_x_588_, lean_object* v_x_589_, lean_object* v_x_590_){
_start:
{
size_t v_x_8697__boxed_591_; lean_object* v_res_592_; 
v_x_8697__boxed_591_ = lean_unbox_usize(v_x_589_);
lean_dec(v_x_589_);
v_res_592_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0(v_00_u03b2_587_, v_x_588_, v_x_8697__boxed_591_, v_x_590_);
lean_dec(v_x_590_);
lean_dec_ref(v_x_588_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2(lean_object* v_00_u03b2_593_, lean_object* v_x_594_, lean_object* v_x_595_, lean_object* v_x_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2___redArg(v_x_594_, v_x_595_, v_x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_598_, lean_object* v_keys_599_, lean_object* v_vals_600_, lean_object* v_heq_601_, lean_object* v_i_602_, lean_object* v_k_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg(v_keys_599_, v_vals_600_, v_i_602_, v_k_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_605_, lean_object* v_keys_606_, lean_object* v_vals_607_, lean_object* v_heq_608_, lean_object* v_i_609_, lean_object* v_k_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2(v_00_u03b2_605_, v_keys_606_, v_vals_607_, v_heq_608_, v_i_609_, v_k_610_);
lean_dec(v_k_610_);
lean_dec_ref(v_vals_607_);
lean_dec_ref(v_keys_606_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_612_, lean_object* v_x_613_, size_t v_x_614_, size_t v_x_615_, lean_object* v_x_616_, lean_object* v_x_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_x_613_, v_x_614_, v_x_615_, v_x_616_, v_x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_619_, lean_object* v_x_620_, lean_object* v_x_621_, lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
size_t v_x_8718__boxed_625_; size_t v_x_8719__boxed_626_; lean_object* v_res_627_; 
v_x_8718__boxed_625_ = lean_unbox_usize(v_x_621_);
lean_dec(v_x_621_);
v_x_8719__boxed_626_ = lean_unbox_usize(v_x_622_);
lean_dec(v_x_622_);
v_res_627_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5(v_00_u03b2_619_, v_x_620_, v_x_8718__boxed_625_, v_x_8719__boxed_626_, v_x_623_, v_x_624_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_628_, lean_object* v_n_629_, lean_object* v_k_630_, lean_object* v_v_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8___redArg(v_n_629_, v_k_630_, v_v_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_633_, size_t v_depth_634_, lean_object* v_keys_635_, lean_object* v_vals_636_, lean_object* v_heq_637_, lean_object* v_i_638_, lean_object* v_entries_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(v_depth_634_, v_keys_635_, v_vals_636_, v_i_638_, v_entries_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03b2_641_, lean_object* v_depth_642_, lean_object* v_keys_643_, lean_object* v_vals_644_, lean_object* v_heq_645_, lean_object* v_i_646_, lean_object* v_entries_647_){
_start:
{
size_t v_depth_boxed_648_; lean_object* v_res_649_; 
v_depth_boxed_648_ = lean_unbox_usize(v_depth_642_);
lean_dec(v_depth_642_);
v_res_649_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9(v_00_u03b2_641_, v_depth_boxed_648_, v_keys_643_, v_vals_644_, v_heq_645_, v_i_646_, v_entries_647_);
lean_dec_ref(v_vals_644_);
lean_dec_ref(v_keys_643_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8_spec__9(lean_object* v_00_u03b2_650_, lean_object* v_x_651_, lean_object* v_x_652_, lean_object* v_x_653_, lean_object* v_x_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8_spec__9___redArg(v_x_651_, v_x_652_, v_x_653_, v_x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel_x3f(lean_object* v_u_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v___x_662_; uint8_t v___x_663_; lean_object* v___x_664_; 
v___x_662_ = lean_st_ref_get(v_a_658_);
v___x_663_ = 1;
v___x_664_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(v_u_656_, v___x_663_, v_a_657_, v_a_658_, v_a_659_, v_a_660_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
if (lean_obj_tag(v_a_665_) == 0)
{
lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_687_; 
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_687_ == 0)
{
lean_object* v_unused_688_; 
v_unused_688_ = lean_ctor_get(v___x_664_, 0);
lean_dec(v_unused_688_);
v___x_667_ = v___x_664_;
v_isShared_668_ = v_isSharedCheck_687_;
goto v_resetjp_666_;
}
else
{
lean_dec(v___x_664_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_687_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v_mctx_670_; lean_object* v_cache_671_; lean_object* v_zetaDeltaFVarIds_672_; lean_object* v_postponed_673_; lean_object* v_diag_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_685_; 
v___x_669_ = lean_st_ref_take(v_a_658_);
v_mctx_670_ = lean_ctor_get(v___x_662_, 0);
lean_inc_ref(v_mctx_670_);
lean_dec(v___x_662_);
v_cache_671_ = lean_ctor_get(v___x_669_, 1);
v_zetaDeltaFVarIds_672_ = lean_ctor_get(v___x_669_, 2);
v_postponed_673_ = lean_ctor_get(v___x_669_, 3);
v_diag_674_ = lean_ctor_get(v___x_669_, 4);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_685_ == 0)
{
lean_object* v_unused_686_; 
v_unused_686_ = lean_ctor_get(v___x_669_, 0);
lean_dec(v_unused_686_);
v___x_676_ = v___x_669_;
v_isShared_677_ = v_isSharedCheck_685_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_diag_674_);
lean_inc(v_postponed_673_);
lean_inc(v_zetaDeltaFVarIds_672_);
lean_inc(v_cache_671_);
lean_dec(v___x_669_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_685_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v_mctx_670_);
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_mctx_670_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_cache_671_);
lean_ctor_set(v_reuseFailAlloc_684_, 2, v_zetaDeltaFVarIds_672_);
lean_ctor_set(v_reuseFailAlloc_684_, 3, v_postponed_673_);
lean_ctor_set(v_reuseFailAlloc_684_, 4, v_diag_674_);
v___x_679_ = v_reuseFailAlloc_684_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_680_ = lean_st_ref_put(v_a_658_, v___x_679_);
if (v_isShared_668_ == 0)
{
v___x_682_ = v___x_667_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_665_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_a_665_, 1);
lean_dec(v___x_662_);
return v___x_664_;
}
}
else
{
lean_dec(v___x_662_);
return v___x_664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel_x3f___boxed(lean_object* v_u_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_Meta_decLevel_x3f(v_u_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
lean_dec(v_a_691_);
lean_dec_ref(v_a_690_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(lean_object* v_msg_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_ref_702_; lean_object* v___x_703_; lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_712_; 
v_ref_702_ = lean_ctor_get(v___y_699_, 5);
v___x_703_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4(v_msg_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
v_a_704_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_712_ == 0)
{
v___x_706_ = v___x_703_;
v_isShared_707_ = v_isSharedCheck_712_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_703_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_712_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; lean_object* v___x_710_; 
lean_inc(v_ref_702_);
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v_ref_702_);
lean_ctor_set(v___x_708_, 1, v_a_704_);
if (v_isShared_707_ == 0)
{
lean_ctor_set_tag(v___x_706_, 1);
lean_ctor_set(v___x_706_, 0, v___x_708_);
v___x_710_ = v___x_706_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg___boxed(lean_object* v_msg_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(v_msg_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
return v_res_719_;
}
}
static lean_object* _init_l_Lean_Meta_decLevel___closed__1(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = ((lean_object*)(l_Lean_Meta_decLevel___closed__0));
v___x_722_ = l_Lean_stringToMessageData(v___x_721_);
return v___x_722_;
}
}
static lean_object* _init_l_Lean_Meta_decLevel___closed__3(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = ((lean_object*)(l_Lean_Meta_decLevel___closed__2));
v___x_725_ = l_Lean_stringToMessageData(v___x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel(lean_object* v_u_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v___x_732_; 
lean_inc(v_u_726_);
v___x_732_ = l_Lean_Meta_decLevel_x3f(v_u_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_747_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_747_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_747_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_747_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
if (lean_obj_tag(v_a_733_) == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
lean_del_object(v___x_735_);
v___x_737_ = lean_obj_once(&l_Lean_Meta_decLevel___closed__1, &l_Lean_Meta_decLevel___closed__1_once, _init_l_Lean_Meta_decLevel___closed__1);
v___x_738_ = l_Lean_MessageData_ofLevel(v_u_726_);
v___x_739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_737_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = lean_obj_once(&l_Lean_Meta_decLevel___closed__3, &l_Lean_Meta_decLevel___closed__3_once, _init_l_Lean_Meta_decLevel___closed__3);
v___x_741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_739_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(v___x_741_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
return v___x_742_;
}
else
{
lean_object* v_val_743_; lean_object* v___x_745_; 
lean_dec(v_u_726_);
v_val_743_ = lean_ctor_get(v_a_733_, 0);
lean_inc(v_val_743_);
lean_dec_ref_known(v_a_733_, 1);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v_val_743_);
v___x_745_ = v___x_735_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_val_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec(v_u_726_);
v_a_748_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_732_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_732_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel___boxed(lean_object* v_u_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_Meta_decLevel(v_u_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0(lean_object* v_00_u03b1_763_, lean_object* v_msg_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(v_msg_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___boxed(lean_object* v_00_u03b1_771_, lean_object* v_msg_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0(v_00_u03b1_771_, v_msg_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel(lean_object* v_type_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_Meta_getLevel(v_type_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_787_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_785_, 1);
v___x_787_ = l_Lean_Meta_normalizeLevel(v_a_786_, v_a_780_, v_a_781_, v_a_782_, v_a_783_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_789_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref_known(v___x_787_, 1);
v___x_789_ = l_Lean_Meta_decLevel(v_a_788_, v_a_780_, v_a_781_, v_a_782_, v_a_783_);
return v___x_789_;
}
else
{
return v___x_787_;
}
}
else
{
return v___x_785_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel___boxed(lean_object* v_type_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_Meta_getDecLevel(v_type_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
lean_dec(v_a_794_);
lean_dec_ref(v_a_793_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel_x3f(lean_object* v_type_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_Meta_getLevel(v_type_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_805_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 1);
v___x_805_ = l_Lean_Meta_normalizeLevel(v_a_804_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_807_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref_known(v___x_805_, 1);
v___x_807_ = l_Lean_Meta_decLevel_x3f(v_a_806_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
return v___x_807_;
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
v_a_808_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_805_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_805_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
v_a_816_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_803_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_803_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel_x3f___boxed(lean_object* v_type_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_Meta_getDecLevel_x3f(v_type_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
return v_res_830_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_872_ = lean_unsigned_to_nat(3263537904u);
v___x_873_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_));
v___x_874_ = l_Lean_Name_num___override(v___x_873_, v___x_872_);
return v___x_874_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_876_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_));
v___x_877_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_);
v___x_878_ = l_Lean_Name_str___override(v___x_877_, v___x_876_);
return v___x_878_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_880_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_));
v___x_881_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_);
v___x_882_ = l_Lean_Name_str___override(v___x_881_, v___x_880_);
return v___x_882_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_883_ = lean_unsigned_to_nat(2u);
v___x_884_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_);
v___x_885_ = l_Lean_Name_num___override(v___x_884_, v___x_883_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_887_; uint8_t v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_887_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3));
v___x_888_ = 0;
v___x_889_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_);
v___x_890_ = l_Lean_registerTraceClass(v___x_887_, v___x_888_, v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2____boxed(lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_();
return v_res_892_;
}
}
lean_object* runtime_initialize_Lean_Meta_InferType(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_DecLevel(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_DecLevel(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_DecLevel(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_DecLevel(builtin);
}
#ifdef __cplusplus
}
#endif
