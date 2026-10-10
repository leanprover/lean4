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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3(lean_object* v_msg_2_, uint8_t v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___f_9_; lean_object* v___f_10_; lean_object* v___x_6677__overap_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___f_9_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3___closed__0));
v___f_10_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_10_, 0, v___f_9_);
v___x_6677__overap_11_ = lean_panic_fn_borrowed(v___f_10_, v_msg_2_);
lean_dec_ref(v___f_10_);
v___x_12_ = lean_box(v___y_3_);
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_5_);
lean_inc_ref(v___y_4_);
v___x_13_ = lean_apply_6(v___x_6677__overap_11_, v___x_12_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_13_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2_ = stack[0].m_obj;
uint8_t v___y_3_ = stack[1].m_num;
lean_object* v___y_4_ = stack[2].m_obj;
lean_object* v___y_5_ = stack[3].m_obj;
lean_object* v___y_6_ = stack[4].m_obj;
lean_object* v___y_7_ = stack[5].m_obj;
lean_object* v_res_14_;
v_res_14_ = l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3(v_msg_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_);
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3___boxed(lean_object* v_msg_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
uint8_t v___y_7570__boxed_22_; lean_object* v_res_23_; 
v___y_7570__boxed_22_ = lean_unbox(v___y_16_);
v_res_23_ = l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3(v_msg_15_, v___y_7570__boxed_22_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_23_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4(lean_object* v_msgData_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v___x_30_; lean_object* v_env_31_; uint8_t v___x_32_; lean_object* v_env_33_; lean_object* v___x_34_; lean_object* v_toCold_35_; lean_object* v_mctx_36_; lean_object* v_lctx_37_; lean_object* v_options_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_30_ = lean_st_ref_get(v___y_28_);
v_env_31_ = lean_ctor_get(v___x_30_, 0);
lean_inc_ref(v_env_31_);
lean_dec(v___x_30_);
v___x_32_ = 0;
v_env_33_ = l_Lean_Environment_setRecordingDeps(v_env_31_, v___x_32_);
v___x_34_ = lean_st_ref_get(v___y_26_);
v_toCold_35_ = lean_ctor_get(v___y_27_, 0);
v_mctx_36_ = lean_ctor_get(v___x_34_, 0);
lean_inc_ref(v_mctx_36_);
lean_dec(v___x_34_);
v_lctx_37_ = lean_ctor_get(v___y_25_, 2);
v_options_38_ = lean_ctor_get(v_toCold_35_, 2);
lean_inc_ref(v_options_38_);
lean_inc_ref(v_lctx_37_);
v___x_39_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_39_, 0, v_env_33_);
lean_ctor_set(v___x_39_, 1, v_mctx_36_);
lean_ctor_set(v___x_39_, 2, v_lctx_37_);
lean_ctor_set(v___x_39_, 3, v_options_38_);
v___x_40_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
lean_ctor_set(v___x_40_, 1, v_msgData_24_);
v___x_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_24_ = stack[0].m_obj;
lean_object* v___y_25_ = stack[1].m_obj;
lean_object* v___y_26_ = stack[2].m_obj;
lean_object* v___y_27_ = stack[3].m_obj;
lean_object* v___y_28_ = stack[4].m_obj;
lean_object* v_res_42_;
v_res_42_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4(v_msgData_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
stack->m_obj
 = v_res_42_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4___boxed(lean_object* v_msgData_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4(v_msgData_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
return v_res_49_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_50_; double v___x_51_; 
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = lean_float_of_nat(v___x_50_);
return v___x_51_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg(lean_object* v_cls_55_, lean_object* v_msg_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v_ref_62_; lean_object* v___x_63_; lean_object* v_a_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_109_; 
v_ref_62_ = lean_ctor_get(v___y_59_, 2);
v___x_63_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4(v_msg_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
v_a_64_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_109_ == 0)
{
v___x_66_ = v___x_63_;
v_isShared_67_ = v_isSharedCheck_109_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_a_64_);
lean_dec(v___x_63_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_109_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_68_; lean_object* v_traceState_69_; lean_object* v_env_70_; lean_object* v_nextMacroScope_71_; lean_object* v_ngen_72_; lean_object* v_auxDeclNGen_73_; lean_object* v_cache_74_; lean_object* v_recordedDeps_75_; lean_object* v_messages_76_; lean_object* v_infoState_77_; lean_object* v_snapshotTasks_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_108_; 
v___x_68_ = lean_st_ref_take(v___y_60_);
v_traceState_69_ = lean_ctor_get(v___x_68_, 4);
v_env_70_ = lean_ctor_get(v___x_68_, 0);
v_nextMacroScope_71_ = lean_ctor_get(v___x_68_, 1);
v_ngen_72_ = lean_ctor_get(v___x_68_, 2);
v_auxDeclNGen_73_ = lean_ctor_get(v___x_68_, 3);
v_cache_74_ = lean_ctor_get(v___x_68_, 5);
v_recordedDeps_75_ = lean_ctor_get(v___x_68_, 6);
v_messages_76_ = lean_ctor_get(v___x_68_, 7);
v_infoState_77_ = lean_ctor_get(v___x_68_, 8);
v_snapshotTasks_78_ = lean_ctor_get(v___x_68_, 9);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_108_ == 0)
{
v___x_80_ = v___x_68_;
v_isShared_81_ = v_isSharedCheck_108_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_snapshotTasks_78_);
lean_inc(v_infoState_77_);
lean_inc(v_messages_76_);
lean_inc(v_recordedDeps_75_);
lean_inc(v_cache_74_);
lean_inc(v_traceState_69_);
lean_inc(v_auxDeclNGen_73_);
lean_inc(v_ngen_72_);
lean_inc(v_nextMacroScope_71_);
lean_inc(v_env_70_);
lean_dec(v___x_68_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_108_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
uint64_t v_tid_82_; lean_object* v_traces_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_107_; 
v_tid_82_ = lean_ctor_get_uint64(v_traceState_69_, sizeof(void*)*1);
v_traces_83_ = lean_ctor_get(v_traceState_69_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v_traceState_69_);
if (v_isSharedCheck_107_ == 0)
{
v___x_85_ = v_traceState_69_;
v_isShared_86_ = v_isSharedCheck_107_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_traces_83_);
lean_dec(v_traceState_69_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_107_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; lean_object* v___x_88_; double v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_87_ = lean_box(0);
v___x_88_ = lean_box(0);
v___x_89_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__0);
v___x_90_ = 0;
v___x_91_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__1));
v___x_92_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_92_, 0, v_cls_55_);
lean_ctor_set(v___x_92_, 1, v___x_88_);
lean_ctor_set(v___x_92_, 2, v___x_91_);
lean_ctor_set_float(v___x_92_, sizeof(void*)*3, v___x_89_);
lean_ctor_set_float(v___x_92_, sizeof(void*)*3 + 8, v___x_89_);
lean_ctor_set_uint8(v___x_92_, sizeof(void*)*3 + 16, v___x_90_);
v___x_93_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__2));
v___x_94_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_94_, 0, v___x_92_);
lean_ctor_set(v___x_94_, 1, v_a_64_);
lean_ctor_set(v___x_94_, 2, v___x_93_);
lean_inc(v_ref_62_);
v___x_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_95_, 0, v_ref_62_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_96_ = l_Lean_PersistentArray_push___redArg(v_traces_83_, v___x_95_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_96_);
v___x_98_ = v___x_85_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_96_);
lean_ctor_set_uint64(v_reuseFailAlloc_106_, sizeof(void*)*1, v_tid_82_);
v___x_98_ = v_reuseFailAlloc_106_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v___x_100_; 
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 4, v___x_98_);
v___x_100_ = v___x_80_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_env_70_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_nextMacroScope_71_);
lean_ctor_set(v_reuseFailAlloc_105_, 2, v_ngen_72_);
lean_ctor_set(v_reuseFailAlloc_105_, 3, v_auxDeclNGen_73_);
lean_ctor_set(v_reuseFailAlloc_105_, 4, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_105_, 5, v_cache_74_);
lean_ctor_set(v_reuseFailAlloc_105_, 6, v_recordedDeps_75_);
lean_ctor_set(v_reuseFailAlloc_105_, 7, v_messages_76_);
lean_ctor_set(v_reuseFailAlloc_105_, 8, v_infoState_77_);
lean_ctor_set(v_reuseFailAlloc_105_, 9, v_snapshotTasks_78_);
v___x_100_ = v_reuseFailAlloc_105_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_101_ = lean_st_ref_put(v___y_60_, v___x_100_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 0, v___x_87_);
v___x_103_ = v___x_66_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_87_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_55_ = stack[0].m_obj;
lean_object* v_msg_56_ = stack[1].m_obj;
lean_object* v___y_57_ = stack[2].m_obj;
lean_object* v___y_58_ = stack[3].m_obj;
lean_object* v___y_59_ = stack[4].m_obj;
lean_object* v___y_60_ = stack[5].m_obj;
lean_object* v_res_110_;
v_res_110_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg(v_cls_55_, v_msg_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
stack->m_obj
 = v_res_110_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___boxed(lean_object* v_cls_111_, lean_object* v_msg_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg(v_cls_111_, v_msg_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8_spec__9___redArg(lean_object* v_x_119_, lean_object* v_x_120_, lean_object* v_x_121_, lean_object* v_x_122_){
_start:
{
lean_object* v_ks_123_; lean_object* v_vs_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_148_; 
v_ks_123_ = lean_ctor_get(v_x_119_, 0);
v_vs_124_ = lean_ctor_get(v_x_119_, 1);
v_isSharedCheck_148_ = !lean_is_exclusive(v_x_119_);
if (v_isSharedCheck_148_ == 0)
{
v___x_126_ = v_x_119_;
v_isShared_127_ = v_isSharedCheck_148_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_vs_124_);
lean_inc(v_ks_123_);
lean_dec(v_x_119_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_148_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = lean_array_get_size(v_ks_123_);
v___x_129_ = lean_nat_dec_lt(v_x_120_, v___x_128_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
lean_dec(v_x_120_);
v___x_130_ = lean_array_push(v_ks_123_, v_x_121_);
v___x_131_ = lean_array_push(v_vs_124_, v_x_122_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v___x_131_);
lean_ctor_set(v___x_126_, 0, v___x_130_);
v___x_133_ = v___x_126_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_130_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
else
{
lean_object* v_k_x27_135_; uint8_t v___x_136_; 
v_k_x27_135_ = lean_array_fget_borrowed(v_ks_123_, v_x_120_);
v___x_136_ = l_Lean_instBEqLevelMVarId_beq(v_x_121_, v_k_x27_135_);
if (v___x_136_ == 0)
{
lean_object* v___x_138_; 
if (v_isShared_127_ == 0)
{
v___x_138_ = v___x_126_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_ks_123_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_vs_124_);
v___x_138_ = v_reuseFailAlloc_142_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_unsigned_to_nat(1u);
v___x_140_ = lean_nat_add(v_x_120_, v___x_139_);
lean_dec(v_x_120_);
v_x_119_ = v___x_138_;
v_x_120_ = v___x_140_;
goto _start;
}
}
else
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_143_ = lean_array_fset(v_ks_123_, v_x_120_, v_x_121_);
v___x_144_ = lean_array_fset(v_vs_124_, v_x_120_, v_x_122_);
lean_dec(v_x_120_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 1, v___x_144_);
lean_ctor_set(v___x_126_, 0, v___x_143_);
v___x_146_ = v___x_126_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_143_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v___x_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_n_149_, lean_object* v_k_150_, lean_object* v_v_151_){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8_spec__9___redArg(v_n_149_, v___x_152_, v_k_150_, v_v_151_);
return v___x_153_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_154_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(lean_object* v_x_155_, size_t v_x_156_, size_t v_x_157_, lean_object* v_x_158_, lean_object* v_x_159_){
_start:
{
if (lean_obj_tag(v_x_155_) == 0)
{
lean_object* v_es_160_; size_t v___x_161_; size_t v___x_162_; lean_object* v_j_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v_es_160_ = lean_ctor_get(v_x_155_, 0);
v___x_161_ = ((size_t)31ULL);
v___x_162_ = lean_usize_land(v_x_156_, v___x_161_);
v_j_163_ = lean_usize_to_nat(v___x_162_);
v___x_164_ = lean_array_get_size(v_es_160_);
v___x_165_ = lean_nat_dec_lt(v_j_163_, v___x_164_);
if (v___x_165_ == 0)
{
lean_dec(v_j_163_);
lean_dec(v_x_159_);
lean_dec(v_x_158_);
return v_x_155_;
}
else
{
lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_204_; 
lean_inc_ref(v_es_160_);
v_isSharedCheck_204_ = !lean_is_exclusive(v_x_155_);
if (v_isSharedCheck_204_ == 0)
{
lean_object* v_unused_205_; 
v_unused_205_ = lean_ctor_get(v_x_155_, 0);
lean_dec(v_unused_205_);
v___x_167_ = v_x_155_;
v_isShared_168_ = v_isSharedCheck_204_;
goto v_resetjp_166_;
}
else
{
lean_dec(v_x_155_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_204_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v_v_169_; lean_object* v___x_170_; lean_object* v_xs_x27_171_; lean_object* v___y_173_; 
v_v_169_ = lean_array_fget(v_es_160_, v_j_163_);
v___x_170_ = lean_box(0);
v_xs_x27_171_ = lean_array_fset(v_es_160_, v_j_163_, v___x_170_);
switch(lean_obj_tag(v_v_169_))
{
case 0:
{
lean_object* v_key_178_; lean_object* v_val_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_189_; 
v_key_178_ = lean_ctor_get(v_v_169_, 0);
v_val_179_ = lean_ctor_get(v_v_169_, 1);
v_isSharedCheck_189_ = !lean_is_exclusive(v_v_169_);
if (v_isSharedCheck_189_ == 0)
{
v___x_181_ = v_v_169_;
v_isShared_182_ = v_isSharedCheck_189_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_val_179_);
lean_inc(v_key_178_);
lean_dec(v_v_169_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_189_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
uint8_t v___x_183_; 
v___x_183_ = l_Lean_instBEqLevelMVarId_beq(v_x_158_, v_key_178_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; 
lean_del_object(v___x_181_);
v___x_184_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_178_, v_val_179_, v_x_158_, v_x_159_);
v___x_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
v___y_173_ = v___x_185_;
goto v___jp_172_;
}
else
{
lean_object* v___x_187_; 
lean_dec(v_val_179_);
lean_dec(v_key_178_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 1, v_x_159_);
lean_ctor_set(v___x_181_, 0, v_x_158_);
v___x_187_ = v___x_181_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_x_158_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_x_159_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
v___y_173_ = v___x_187_;
goto v___jp_172_;
}
}
}
}
case 1:
{
lean_object* v_node_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_202_; 
v_node_190_ = lean_ctor_get(v_v_169_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v_v_169_);
if (v_isSharedCheck_202_ == 0)
{
v___x_192_ = v_v_169_;
v_isShared_193_ = v_isSharedCheck_202_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_node_190_);
lean_dec(v_v_169_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_202_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
size_t v___x_194_; size_t v___x_195_; size_t v___x_196_; size_t v___x_197_; lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_194_ = ((size_t)5ULL);
v___x_195_ = lean_usize_shift_right(v_x_156_, v___x_194_);
v___x_196_ = ((size_t)1ULL);
v___x_197_ = lean_usize_add(v_x_157_, v___x_196_);
v___x_198_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_node_190_, v___x_195_, v___x_197_, v_x_158_, v_x_159_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_198_);
v___x_200_ = v___x_192_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_198_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
v___y_173_ = v___x_200_;
goto v___jp_172_;
}
}
}
default: 
{
lean_object* v___x_203_; 
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v_x_158_);
lean_ctor_set(v___x_203_, 1, v_x_159_);
v___y_173_ = v___x_203_;
goto v___jp_172_;
}
}
v___jp_172_:
{
lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_174_ = lean_array_fset(v_xs_x27_171_, v_j_163_, v___y_173_);
lean_dec(v_j_163_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_174_);
v___x_176_ = v___x_167_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
else
{
lean_object* v_ks_206_; lean_object* v_vs_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_225_; 
v_ks_206_ = lean_ctor_get(v_x_155_, 0);
v_vs_207_ = lean_ctor_get(v_x_155_, 1);
v_isSharedCheck_225_ = !lean_is_exclusive(v_x_155_);
if (v_isSharedCheck_225_ == 0)
{
v___x_209_ = v_x_155_;
v_isShared_210_ = v_isSharedCheck_225_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_vs_207_);
lean_inc(v_ks_206_);
lean_dec(v_x_155_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_225_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_ks_206_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_vs_207_);
v___x_212_ = v_reuseFailAlloc_224_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v_newNode_213_; size_t v___x_214_; uint8_t v___x_215_; 
v_newNode_213_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8___redArg(v___x_212_, v_x_158_, v_x_159_);
v___x_214_ = ((size_t)7ULL);
v___x_215_ = lean_usize_dec_le(v___x_214_, v_x_157_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_216_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_213_);
v___x_217_ = lean_unsigned_to_nat(4u);
v___x_218_ = lean_nat_dec_lt(v___x_216_, v___x_217_);
lean_dec(v___x_216_);
if (v___x_218_ == 0)
{
lean_object* v_ks_219_; lean_object* v_vs_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v_ks_219_ = lean_ctor_get(v_newNode_213_, 0);
lean_inc_ref(v_ks_219_);
v_vs_220_ = lean_ctor_get(v_newNode_213_, 1);
lean_inc_ref(v_vs_220_);
lean_dec_ref(v_newNode_213_);
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_223_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(v_x_157_, v_ks_219_, v_vs_220_, v___x_221_, v___x_222_);
lean_dec_ref(v_vs_220_);
lean_dec_ref(v_ks_219_);
return v___x_223_;
}
else
{
return v_newNode_213_;
}
}
else
{
return v_newNode_213_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_155_ = stack[0].m_obj;
size_t v_x_156_ = stack[1].m_num;
size_t v_x_157_ = stack[2].m_num;
lean_object* v_x_158_ = stack[3].m_obj;
lean_object* v_x_159_ = stack[4].m_obj;
lean_object* v_res_226_;
v_res_226_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_x_155_, v_x_156_, v_x_157_, v_x_158_, v_x_159_);
stack->m_obj
 = v_res_226_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(size_t v_depth_227_, lean_object* v_keys_228_, lean_object* v_vals_229_, lean_object* v_i_230_, lean_object* v_entries_231_){
_start:
{
lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_232_ = lean_array_get_size(v_keys_228_);
v___x_233_ = lean_nat_dec_lt(v_i_230_, v___x_232_);
if (v___x_233_ == 0)
{
lean_dec(v_i_230_);
return v_entries_231_;
}
else
{
lean_object* v_k_234_; lean_object* v_v_235_; uint64_t v___x_236_; size_t v_h_237_; size_t v___x_238_; lean_object* v___x_239_; size_t v___x_240_; size_t v___x_241_; size_t v___x_242_; size_t v_h_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_k_234_ = lean_array_fget_borrowed(v_keys_228_, v_i_230_);
v_v_235_ = lean_array_fget_borrowed(v_vals_229_, v_i_230_);
v___x_236_ = l_Lean_instHashableLevelMVarId_hash(v_k_234_);
v_h_237_ = lean_uint64_to_usize(v___x_236_);
v___x_238_ = ((size_t)5ULL);
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = ((size_t)1ULL);
v___x_241_ = lean_usize_sub(v_depth_227_, v___x_240_);
v___x_242_ = lean_usize_mul(v___x_238_, v___x_241_);
v_h_243_ = lean_usize_shift_right(v_h_237_, v___x_242_);
v___x_244_ = lean_nat_add(v_i_230_, v___x_239_);
lean_dec(v_i_230_);
lean_inc(v_v_235_);
lean_inc(v_k_234_);
v___x_245_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_entries_231_, v_h_243_, v_depth_227_, v_k_234_, v_v_235_);
v_i_230_ = v___x_244_;
v_entries_231_ = v___x_245_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_227_ = stack[0].m_num;
lean_object* v_keys_228_ = stack[1].m_obj;
lean_object* v_vals_229_ = stack[2].m_obj;
lean_object* v_i_230_ = stack[3].m_obj;
lean_object* v_entries_231_ = stack[4].m_obj;
lean_object* v_res_247_;
v_res_247_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(v_depth_227_, v_keys_228_, v_vals_229_, v_i_230_, v_entries_231_);
stack->m_obj
 = v_res_247_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_depth_248_, lean_object* v_keys_249_, lean_object* v_vals_250_, lean_object* v_i_251_, lean_object* v_entries_252_){
_start:
{
size_t v_depth_boxed_253_; lean_object* v_res_254_; 
v_depth_boxed_253_ = lean_unbox_usize(v_depth_248_);
lean_dec(v_depth_248_);
v_res_254_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(v_depth_boxed_253_, v_keys_249_, v_vals_250_, v_i_251_, v_entries_252_);
lean_dec_ref(v_vals_250_);
lean_dec_ref(v_keys_249_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_x_255_, lean_object* v_x_256_, lean_object* v_x_257_, lean_object* v_x_258_, lean_object* v_x_259_){
_start:
{
size_t v_x_7916__boxed_260_; size_t v_x_7917__boxed_261_; lean_object* v_res_262_; 
v_x_7916__boxed_260_ = lean_unbox_usize(v_x_256_);
lean_dec(v_x_256_);
v_x_7917__boxed_261_ = lean_unbox_usize(v_x_257_);
lean_dec(v_x_257_);
v_res_262_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_x_255_, v_x_7916__boxed_260_, v_x_7917__boxed_261_, v_x_258_, v_x_259_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2___redArg(lean_object* v_x_263_, lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
uint64_t v___x_266_; size_t v___x_267_; size_t v___x_268_; lean_object* v___x_269_; 
v___x_266_ = l_Lean_instHashableLevelMVarId_hash(v_x_264_);
v___x_267_ = lean_uint64_to_usize(v___x_266_);
v___x_268_ = ((size_t)1ULL);
v___x_269_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_x_263_, v___x_267_, v___x_268_, v_x_264_, v_x_265_);
return v___x_269_;
}
}
lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(lean_object* v_mvarId_270_, lean_object* v_val_271_, lean_object* v___y_272_){
_start:
{
lean_object* v___x_274_; lean_object* v_mctx_275_; lean_object* v_cache_276_; lean_object* v_zetaDeltaFVarIds_277_; lean_object* v_postponed_278_; lean_object* v_diag_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_309_; 
v___x_274_ = lean_st_ref_take(v___y_272_);
v_mctx_275_ = lean_ctor_get(v___x_274_, 0);
v_cache_276_ = lean_ctor_get(v___x_274_, 1);
v_zetaDeltaFVarIds_277_ = lean_ctor_get(v___x_274_, 2);
v_postponed_278_ = lean_ctor_get(v___x_274_, 3);
v_diag_279_ = lean_ctor_get(v___x_274_, 4);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_309_ == 0)
{
v___x_281_ = v___x_274_;
v_isShared_282_ = v_isSharedCheck_309_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_diag_279_);
lean_inc(v_postponed_278_);
lean_inc(v_zetaDeltaFVarIds_277_);
lean_inc(v_cache_276_);
lean_inc(v_mctx_275_);
lean_dec(v___x_274_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_309_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v_depth_283_; lean_object* v_levelAssignDepth_284_; lean_object* v_lmvarCounter_285_; lean_object* v_mvarCounter_286_; lean_object* v_lDecls_287_; lean_object* v_decls_288_; lean_object* v_userNames_289_; lean_object* v_lAssignment_290_; lean_object* v_eAssignment_291_; lean_object* v_dAssignment_292_; lean_object* v_instanceTypedMVars_293_; lean_object* v_synthNormMemo_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_308_; 
v_depth_283_ = lean_ctor_get(v_mctx_275_, 0);
v_levelAssignDepth_284_ = lean_ctor_get(v_mctx_275_, 1);
v_lmvarCounter_285_ = lean_ctor_get(v_mctx_275_, 2);
v_mvarCounter_286_ = lean_ctor_get(v_mctx_275_, 3);
v_lDecls_287_ = lean_ctor_get(v_mctx_275_, 4);
v_decls_288_ = lean_ctor_get(v_mctx_275_, 5);
v_userNames_289_ = lean_ctor_get(v_mctx_275_, 6);
v_lAssignment_290_ = lean_ctor_get(v_mctx_275_, 7);
v_eAssignment_291_ = lean_ctor_get(v_mctx_275_, 8);
v_dAssignment_292_ = lean_ctor_get(v_mctx_275_, 9);
v_instanceTypedMVars_293_ = lean_ctor_get(v_mctx_275_, 10);
v_synthNormMemo_294_ = lean_ctor_get(v_mctx_275_, 11);
v_isSharedCheck_308_ = !lean_is_exclusive(v_mctx_275_);
if (v_isSharedCheck_308_ == 0)
{
v___x_296_ = v_mctx_275_;
v_isShared_297_ = v_isSharedCheck_308_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_synthNormMemo_294_);
lean_inc(v_instanceTypedMVars_293_);
lean_inc(v_dAssignment_292_);
lean_inc(v_eAssignment_291_);
lean_inc(v_lAssignment_290_);
lean_inc(v_userNames_289_);
lean_inc(v_decls_288_);
lean_inc(v_lDecls_287_);
lean_inc(v_mvarCounter_286_);
lean_inc(v_lmvarCounter_285_);
lean_inc(v_levelAssignDepth_284_);
lean_inc(v_depth_283_);
lean_dec(v_mctx_275_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_308_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_298_ = lean_box(0);
v___x_299_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2___redArg(v_lAssignment_290_, v_mvarId_270_, v_val_271_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 7, v___x_299_);
v___x_301_ = v___x_296_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_depth_283_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_levelAssignDepth_284_);
lean_ctor_set(v_reuseFailAlloc_307_, 2, v_lmvarCounter_285_);
lean_ctor_set(v_reuseFailAlloc_307_, 3, v_mvarCounter_286_);
lean_ctor_set(v_reuseFailAlloc_307_, 4, v_lDecls_287_);
lean_ctor_set(v_reuseFailAlloc_307_, 5, v_decls_288_);
lean_ctor_set(v_reuseFailAlloc_307_, 6, v_userNames_289_);
lean_ctor_set(v_reuseFailAlloc_307_, 7, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_307_, 8, v_eAssignment_291_);
lean_ctor_set(v_reuseFailAlloc_307_, 9, v_dAssignment_292_);
lean_ctor_set(v_reuseFailAlloc_307_, 10, v_instanceTypedMVars_293_);
lean_ctor_set(v_reuseFailAlloc_307_, 11, v_synthNormMemo_294_);
v___x_301_ = v_reuseFailAlloc_307_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_303_; 
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_301_);
v___x_303_ = v___x_281_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_cache_276_);
lean_ctor_set(v_reuseFailAlloc_306_, 2, v_zetaDeltaFVarIds_277_);
lean_ctor_set(v_reuseFailAlloc_306_, 3, v_postponed_278_);
lean_ctor_set(v_reuseFailAlloc_306_, 4, v_diag_279_);
v___x_303_ = v_reuseFailAlloc_306_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_st_ref_put(v___y_272_, v___x_303_);
v___x_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_298_);
return v___x_305_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_270_ = stack[0].m_obj;
lean_object* v_val_271_ = stack[1].m_obj;
lean_object* v___y_272_ = stack[2].m_obj;
lean_object* v_res_310_;
v_res_310_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(v_mvarId_270_, v_val_271_, v___y_272_);
stack->m_obj
 = v_res_310_;
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_311_, lean_object* v_val_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(v_mvarId_311_, v_val_312_, v___y_313_);
lean_dec(v___y_313_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_316_, lean_object* v_vals_317_, lean_object* v_i_318_, lean_object* v_k_319_){
_start:
{
lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_320_ = lean_array_get_size(v_keys_316_);
v___x_321_ = lean_nat_dec_lt(v_i_318_, v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; 
lean_dec(v_i_318_);
v___x_322_ = lean_box(0);
return v___x_322_;
}
else
{
lean_object* v_k_x27_323_; uint8_t v___x_324_; 
v_k_x27_323_ = lean_array_fget_borrowed(v_keys_316_, v_i_318_);
v___x_324_ = l_Lean_instBEqLevelMVarId_beq(v_k_319_, v_k_x27_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_unsigned_to_nat(1u);
v___x_326_ = lean_nat_add(v_i_318_, v___x_325_);
lean_dec(v_i_318_);
v_i_318_ = v___x_326_;
goto _start;
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_array_fget_borrowed(v_vals_317_, v_i_318_);
lean_dec(v_i_318_);
lean_inc(v___x_328_);
v___x_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
return v___x_329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_330_, lean_object* v_vals_331_, lean_object* v_i_332_, lean_object* v_k_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg(v_keys_330_, v_vals_331_, v_i_332_, v_k_333_);
lean_dec(v_k_333_);
lean_dec_ref(v_vals_331_);
lean_dec_ref(v_keys_330_);
return v_res_334_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(lean_object* v_x_335_, size_t v_x_336_, lean_object* v_x_337_){
_start:
{
if (lean_obj_tag(v_x_335_) == 0)
{
lean_object* v_es_338_; lean_object* v___x_339_; size_t v___x_340_; size_t v___x_341_; lean_object* v_j_342_; lean_object* v___x_343_; 
v_es_338_ = lean_ctor_get(v_x_335_, 0);
v___x_339_ = lean_box(2);
v___x_340_ = ((size_t)31ULL);
v___x_341_ = lean_usize_land(v_x_336_, v___x_340_);
v_j_342_ = lean_usize_to_nat(v___x_341_);
v___x_343_ = lean_array_get_borrowed(v___x_339_, v_es_338_, v_j_342_);
lean_dec(v_j_342_);
switch(lean_obj_tag(v___x_343_))
{
case 0:
{
lean_object* v_key_344_; lean_object* v_val_345_; uint8_t v___x_346_; 
v_key_344_ = lean_ctor_get(v___x_343_, 0);
v_val_345_ = lean_ctor_get(v___x_343_, 1);
v___x_346_ = l_Lean_instBEqLevelMVarId_beq(v_x_337_, v_key_344_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; 
v___x_347_ = lean_box(0);
return v___x_347_;
}
else
{
lean_object* v___x_348_; 
lean_inc(v_val_345_);
v___x_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_348_, 0, v_val_345_);
return v___x_348_;
}
}
case 1:
{
lean_object* v_node_349_; size_t v___x_350_; size_t v___x_351_; 
v_node_349_ = lean_ctor_get(v___x_343_, 0);
v___x_350_ = ((size_t)5ULL);
v___x_351_ = lean_usize_shift_right(v_x_336_, v___x_350_);
v_x_335_ = v_node_349_;
v_x_336_ = v___x_351_;
goto _start;
}
default: 
{
lean_object* v___x_353_; 
v___x_353_ = lean_box(0);
return v___x_353_;
}
}
}
else
{
lean_object* v_ks_354_; lean_object* v_vs_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_ks_354_ = lean_ctor_get(v_x_335_, 0);
v_vs_355_ = lean_ctor_get(v_x_335_, 1);
v___x_356_ = lean_unsigned_to_nat(0u);
v___x_357_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg(v_ks_354_, v_vs_355_, v___x_356_, v_x_337_);
return v___x_357_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_335_ = stack[0].m_obj;
size_t v_x_336_ = stack[1].m_num;
lean_object* v_x_337_ = stack[2].m_obj;
lean_object* v_res_358_;
v_res_358_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(v_x_335_, v_x_336_, v_x_337_);
stack->m_obj
 = v_res_358_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_359_, lean_object* v_x_360_, lean_object* v_x_361_){
_start:
{
size_t v_x_8267__boxed_362_; lean_object* v_res_363_; 
v_x_8267__boxed_362_ = lean_unbox_usize(v_x_360_);
lean_dec(v_x_360_);
v_res_363_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(v_x_359_, v_x_8267__boxed_362_, v_x_361_);
lean_dec(v_x_361_);
lean_dec_ref(v_x_359_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg(lean_object* v_x_364_, lean_object* v_x_365_){
_start:
{
uint64_t v___x_366_; size_t v___x_367_; lean_object* v___x_368_; 
v___x_366_ = l_Lean_instHashableLevelMVarId_hash(v_x_365_);
v___x_367_ = lean_uint64_to_usize(v___x_366_);
v___x_368_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(v_x_364_, v___x_367_, v_x_365_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg___boxed(lean_object* v_x_369_, lean_object* v_x_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg(v_x_369_, v_x_370_);
lean_dec(v_x_370_);
lean_dec_ref(v_x_369_);
return v_res_371_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_382_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3));
v___x_383_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__5));
v___x_384_ = l_Lean_Name_append(v___x_383_, v___x_382_);
return v___x_384_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__7));
v___x_387_ = l_Lean_stringToMessageData(v___x_386_);
return v___x_387_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__9));
v___x_390_ = l_Lean_stringToMessageData(v___x_389_);
return v___x_390_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_394_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__13));
v___x_395_ = lean_unsigned_to_nat(24u);
v___x_396_ = lean_unsigned_to_nat(55u);
v___x_397_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__12));
v___x_398_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__11));
v___x_399_ = l_mkPanicMessageWithDecl(v___x_398_, v___x_397_, v___x_396_, v___x_395_, v___x_394_);
return v___x_399_;
}
}
lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(lean_object* v_x_400_, uint8_t v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v_u_411_; lean_object* v_v_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; 
switch(lean_obj_tag(v_x_400_))
{
case 0:
{
goto v___jp_407_;
}
case 4:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec_ref_known(v_x_400_, 1);
v___x_439_ = lean_box(0);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
return v___x_440_;
}
case 5:
{
lean_object* v_a_441_; lean_object* v___x_442_; lean_object* v_mctx_443_; lean_object* v_lAssignment_444_; lean_object* v___x_445_; 
v_a_441_ = lean_ctor_get(v_x_400_, 0);
lean_inc(v_a_441_);
lean_dec_ref_known(v_x_400_, 1);
v___x_442_ = lean_st_ref_get(v_a_403_);
v_mctx_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc_ref(v_mctx_443_);
lean_dec(v___x_442_);
v_lAssignment_444_ = lean_ctor_get(v_mctx_443_, 7);
lean_inc_ref(v_lAssignment_444_);
lean_dec_ref(v_mctx_443_);
v___x_445_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg(v_lAssignment_444_, v_a_441_);
lean_dec_ref(v_lAssignment_444_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v___x_446_; 
lean_inc(v_a_441_);
v___x_446_ = l_Lean_LMVarId_isReadOnly(v_a_441_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_518_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_518_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_518_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_518_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
uint8_t v___x_451_; 
v___x_451_ = lean_unbox(v_a_447_);
lean_dec(v_a_447_);
if (v___x_451_ == 0)
{
if (v_a_401_ == 0)
{
lean_object* v___x_453_; 
lean_dec(v_a_441_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_445_);
v___x_453_ = v___x_449_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_445_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
else
{
lean_object* v___x_455_; 
lean_del_object(v___x_449_);
v___x_455_ = l_Lean_Meta_mkFreshLevelMVar(v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; uint8_t v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v_toCold_482_; lean_object* v_options_483_; uint8_t v_hasTrace_484_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
lean_dec_ref_known(v___x_455_, 1);
v_toCold_482_ = lean_ctor_get(v_a_404_, 0);
v_options_483_ = lean_ctor_get(v_toCold_482_, 2);
v_hasTrace_484_ = lean_ctor_get_uint8(v_options_483_, sizeof(void*)*1);
if (v_hasTrace_484_ == 0)
{
v___y_458_ = v_a_401_;
v___y_459_ = v_a_402_;
v___y_460_ = v_a_403_;
v___y_461_ = v_a_404_;
v___y_462_ = v_a_405_;
goto v___jp_457_;
}
else
{
lean_object* v_inheritedTraceOptions_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_inheritedTraceOptions_485_ = lean_ctor_get(v_toCold_482_, 11);
v___x_486_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3));
v___x_487_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6_once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6);
v___x_488_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_485_, v_options_483_, v___x_487_);
if (v___x_488_ == 0)
{
v___y_458_ = v_a_401_;
v___y_459_ = v_a_402_;
v___y_460_ = v_a_403_;
v___y_461_ = v_a_404_;
v___y_462_ = v_a_405_;
goto v___jp_457_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_489_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8_once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8);
lean_inc(v_a_441_);
v___x_490_ = l_Lean_mkLevelMVar(v_a_441_);
v___x_491_ = l_Lean_MessageData_ofLevel(v___x_490_);
v___x_492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_489_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10_once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10);
v___x_494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
lean_inc(v_a_456_);
v___x_495_ = l_Lean_Level_succ___override(v_a_456_);
v___x_496_ = l_Lean_MessageData_ofLevel(v___x_495_);
v___x_497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_494_);
lean_ctor_set(v___x_497_, 1, v___x_496_);
v___x_498_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg(v___x_486_, v___x_497_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_dec_ref_known(v___x_498_, 1);
v___y_458_ = v_a_401_;
v___y_459_ = v_a_402_;
v___y_460_ = v_a_403_;
v___y_461_ = v_a_404_;
v___y_462_ = v_a_405_;
goto v___jp_457_;
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_dec(v_a_456_);
lean_dec(v_a_441_);
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
v___jp_457_:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
lean_inc(v_a_456_);
v___x_463_ = l_Lean_Level_succ___override(v_a_456_);
v___x_464_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(v_a_441_, v___x_463_, v___y_460_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_472_; 
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; 
v_unused_473_ = lean_ctor_get(v___x_464_, 0);
lean_dec(v_unused_473_);
v___x_466_ = v___x_464_;
v_isShared_467_ = v_isSharedCheck_472_;
goto v_resetjp_465_;
}
else
{
lean_dec(v___x_464_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_472_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_468_, 0, v_a_456_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_468_);
v___x_470_ = v___x_466_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec(v_a_456_);
v_a_474_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_464_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_464_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
lean_dec(v_a_441_);
v_a_507_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_455_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_455_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
else
{
lean_object* v___x_516_; 
lean_dec(v_a_441_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_445_);
v___x_516_ = v___x_449_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_445_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_dec(v_a_441_);
v_a_519_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_446_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_446_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
else
{
lean_object* v_val_527_; 
lean_dec(v_a_441_);
v_val_527_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_val_527_);
lean_dec_ref_known(v___x_445_, 1);
v_x_400_ = v_val_527_;
goto _start;
}
}
case 1:
{
lean_object* v_a_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v_a_529_ = lean_ctor_get(v_x_400_, 0);
lean_inc(v_a_529_);
lean_dec_ref_known(v_x_400_, 1);
v___x_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_530_, 0, v_a_529_);
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
default: 
{
switch(lean_obj_tag(v_x_400_))
{
case 2:
{
lean_object* v_a_532_; lean_object* v_a_533_; 
v_a_532_ = lean_ctor_get(v_x_400_, 0);
lean_inc(v_a_532_);
v_a_533_ = lean_ctor_get(v_x_400_, 1);
lean_inc(v_a_533_);
lean_dec_ref_known(v_x_400_, 2);
v_u_411_ = v_a_532_;
v_v_412_ = v_a_533_;
v___y_413_ = v_a_402_;
v___y_414_ = v_a_403_;
v___y_415_ = v_a_404_;
v___y_416_ = v_a_405_;
goto v___jp_410_;
}
case 3:
{
lean_object* v_a_534_; lean_object* v_a_535_; 
v_a_534_ = lean_ctor_get(v_x_400_, 0);
lean_inc(v_a_534_);
v_a_535_ = lean_ctor_get(v_x_400_, 1);
lean_inc(v_a_535_);
lean_dec_ref_known(v_x_400_, 2);
v_u_411_ = v_a_534_;
v_v_412_ = v_a_535_;
v___y_413_ = v_a_402_;
v___y_414_ = v_a_403_;
v___y_415_ = v_a_404_;
v___y_416_ = v_a_405_;
goto v___jp_410_;
}
default: 
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec(v_x_400_);
v___x_536_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14_once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14);
v___x_537_ = l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3(v___x_536_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
return v___x_537_;
}
}
}
}
v___jp_407_:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_box(0);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
v___jp_410_:
{
uint8_t v___x_417_; lean_object* v___x_418_; 
v___x_417_ = 0;
v___x_418_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(v_u_411_, v___x_417_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref_known(v___x_418_, 1);
if (lean_obj_tag(v_a_419_) == 0)
{
lean_dec(v_v_412_);
goto v___jp_407_;
}
else
{
lean_object* v_val_420_; lean_object* v___x_421_; 
v_val_420_ = lean_ctor_get(v_a_419_, 0);
lean_inc(v_val_420_);
lean_dec_ref_known(v_a_419_, 1);
v___x_421_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(v_v_412_, v___x_417_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_438_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_438_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_438_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_438_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
if (lean_obj_tag(v_a_422_) == 0)
{
lean_del_object(v___x_424_);
lean_dec(v_val_420_);
goto v___jp_407_;
}
else
{
lean_object* v_val_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_437_; 
v_val_426_ = lean_ctor_get(v_a_422_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v_a_422_);
if (v_isSharedCheck_437_ == 0)
{
v___x_428_ = v_a_422_;
v_isShared_429_ = v_isSharedCheck_437_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_val_426_);
lean_dec(v_a_422_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_437_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_430_ = l_Lean_mkLevelMax_x27(v_val_420_, v_val_426_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_430_);
v___x_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_430_);
v___x_432_ = v_reuseFailAlloc_436_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_434_; 
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_432_);
v___x_434_ = v___x_424_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
}
else
{
lean_dec(v_val_420_);
return v___x_421_;
}
}
}
else
{
lean_dec(v_v_412_);
return v___x_418_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_400_ = stack[0].m_obj;
uint8_t v_a_401_ = stack[1].m_num;
lean_object* v_a_402_ = stack[2].m_obj;
lean_object* v_a_403_ = stack[3].m_obj;
lean_object* v_a_404_ = stack[4].m_obj;
lean_object* v_a_405_ = stack[5].m_obj;
lean_object* v_res_538_;
v_res_538_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(v_x_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
stack->m_obj
 = v_res_538_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___boxed(lean_object* v_x_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
uint8_t v_a_boxed_546_; lean_object* v_res_547_; 
v_a_boxed_546_ = lean_unbox(v_a_540_);
v_res_547_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(v_x_539_, v_a_boxed_546_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0(lean_object* v_00_u03b2_548_, lean_object* v_x_549_, lean_object* v_x_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg(v_x_549_, v_x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___boxed(lean_object* v_00_u03b2_552_, lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0(v_00_u03b2_552_, v_x_553_, v_x_554_);
lean_dec(v_x_554_);
lean_dec_ref(v_x_553_);
return v_res_555_;
}
}
lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1(lean_object* v_mvarId_556_, lean_object* v_val_557_, uint8_t v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(v_mvarId_556_, v_val_557_, v___y_560_);
return v___x_564_;
}
}
LEAN_EXPORT void l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_556_ = stack[0].m_obj;
lean_object* v_val_557_ = stack[1].m_obj;
uint8_t v___y_558_ = stack[2].m_num;
lean_object* v___y_559_ = stack[3].m_obj;
lean_object* v___y_560_ = stack[4].m_obj;
lean_object* v___y_561_ = stack[5].m_obj;
lean_object* v___y_562_ = stack[6].m_obj;
lean_object* v_res_565_;
v_res_565_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1(v_mvarId_556_, v_val_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
stack->m_obj
 = v_res_565_;
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___boxed(lean_object* v_mvarId_566_, lean_object* v_val_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
uint8_t v___y_8866__boxed_574_; lean_object* v_res_575_; 
v___y_8866__boxed_574_ = lean_unbox(v___y_568_);
v_res_575_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1(v_mvarId_566_, v_val_567_, v___y_8866__boxed_574_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
return v_res_575_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2(lean_object* v_cls_576_, lean_object* v_msg_577_, uint8_t v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg(v_cls_576_, v_msg_577_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
return v___x_584_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_576_ = stack[0].m_obj;
lean_object* v_msg_577_ = stack[1].m_obj;
uint8_t v___y_578_ = stack[2].m_num;
lean_object* v___y_579_ = stack[3].m_obj;
lean_object* v___y_580_ = stack[4].m_obj;
lean_object* v___y_581_ = stack[5].m_obj;
lean_object* v___y_582_ = stack[6].m_obj;
lean_object* v_res_585_;
v_res_585_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2(v_cls_576_, v_msg_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
stack->m_obj
 = v_res_585_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___boxed(lean_object* v_cls_586_, lean_object* v_msg_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
uint8_t v___y_8899__boxed_594_; lean_object* v_res_595_; 
v___y_8899__boxed_594_ = lean_unbox(v___y_588_);
v_res_595_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2(v_cls_586_, v_msg_587_, v___y_8899__boxed_594_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
return v_res_595_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0(lean_object* v_00_u03b2_596_, lean_object* v_x_597_, size_t v_x_598_, lean_object* v_x_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(v_x_597_, v_x_598_, v_x_599_);
return v___x_600_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_597_ = stack[1].m_obj;
size_t v_x_598_ = stack[2].m_num;
lean_object* v_x_599_ = stack[3].m_obj;
lean_object* v_res_601_;
v_res_601_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0(lean_box(0), v_x_597_, v_x_598_, v_x_599_);
stack->m_obj
 = v_res_601_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_602_, lean_object* v_x_603_, lean_object* v_x_604_, lean_object* v_x_605_){
_start:
{
size_t v_x_8933__boxed_606_; lean_object* v_res_607_; 
v_x_8933__boxed_606_ = lean_unbox_usize(v_x_604_);
lean_dec(v_x_604_);
v_res_607_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0(v_00_u03b2_602_, v_x_603_, v_x_8933__boxed_606_, v_x_605_);
lean_dec(v_x_605_);
lean_dec_ref(v_x_603_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2(lean_object* v_00_u03b2_608_, lean_object* v_x_609_, lean_object* v_x_610_, lean_object* v_x_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2___redArg(v_x_609_, v_x_610_, v_x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_613_, lean_object* v_keys_614_, lean_object* v_vals_615_, lean_object* v_heq_616_, lean_object* v_i_617_, lean_object* v_k_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg(v_keys_614_, v_vals_615_, v_i_617_, v_k_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_620_, lean_object* v_keys_621_, lean_object* v_vals_622_, lean_object* v_heq_623_, lean_object* v_i_624_, lean_object* v_k_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2(v_00_u03b2_620_, v_keys_621_, v_vals_622_, v_heq_623_, v_i_624_, v_k_625_);
lean_dec(v_k_625_);
lean_dec_ref(v_vals_622_);
lean_dec_ref(v_keys_621_);
return v_res_626_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_627_, lean_object* v_x_628_, size_t v_x_629_, size_t v_x_630_, lean_object* v_x_631_, lean_object* v_x_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_x_628_, v_x_629_, v_x_630_, v_x_631_, v_x_632_);
return v___x_633_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_628_ = stack[1].m_obj;
size_t v_x_629_ = stack[2].m_num;
size_t v_x_630_ = stack[3].m_num;
lean_object* v_x_631_ = stack[4].m_obj;
lean_object* v_x_632_ = stack[5].m_obj;
lean_object* v_res_634_;
v_res_634_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5(lean_box(0), v_x_628_, v_x_629_, v_x_630_, v_x_631_, v_x_632_);
stack->m_obj
 = v_res_634_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_635_, lean_object* v_x_636_, lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_x_640_){
_start:
{
size_t v_x_8966__boxed_641_; size_t v_x_8967__boxed_642_; lean_object* v_res_643_; 
v_x_8966__boxed_641_ = lean_unbox_usize(v_x_637_);
lean_dec(v_x_637_);
v_x_8967__boxed_642_ = lean_unbox_usize(v_x_638_);
lean_dec(v_x_638_);
v_res_643_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5(v_00_u03b2_635_, v_x_636_, v_x_8966__boxed_641_, v_x_8967__boxed_642_, v_x_639_, v_x_640_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_644_, lean_object* v_n_645_, lean_object* v_k_646_, lean_object* v_v_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8___redArg(v_n_645_, v_k_646_, v_v_647_);
return v___x_648_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_649_, size_t v_depth_650_, lean_object* v_keys_651_, lean_object* v_vals_652_, lean_object* v_heq_653_, lean_object* v_i_654_, lean_object* v_entries_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(v_depth_650_, v_keys_651_, v_vals_652_, v_i_654_, v_entries_655_);
return v___x_656_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
size_t v_depth_650_ = stack[1].m_num;
lean_object* v_keys_651_ = stack[2].m_obj;
lean_object* v_vals_652_ = stack[3].m_obj;
lean_object* v_i_654_ = stack[5].m_obj;
lean_object* v_entries_655_ = stack[6].m_obj;
lean_object* v_res_657_;
v_res_657_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9(lean_box(0), v_depth_650_, v_keys_651_, v_vals_652_, lean_box(0), v_i_654_, v_entries_655_);
stack->m_obj
 = v_res_657_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03b2_658_, lean_object* v_depth_659_, lean_object* v_keys_660_, lean_object* v_vals_661_, lean_object* v_heq_662_, lean_object* v_i_663_, lean_object* v_entries_664_){
_start:
{
size_t v_depth_boxed_665_; lean_object* v_res_666_; 
v_depth_boxed_665_ = lean_unbox_usize(v_depth_659_);
lean_dec(v_depth_659_);
v_res_666_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9(v_00_u03b2_658_, v_depth_boxed_665_, v_keys_660_, v_vals_661_, v_heq_662_, v_i_663_, v_entries_664_);
lean_dec_ref(v_vals_661_);
lean_dec_ref(v_keys_660_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8_spec__9(lean_object* v_00_u03b2_667_, lean_object* v_x_668_, lean_object* v_x_669_, lean_object* v_x_670_, lean_object* v_x_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8_spec__9___redArg(v_x_668_, v_x_669_, v_x_670_, v_x_671_);
return v___x_672_;
}
}
lean_object* l_Lean_Meta_decLevel_x3f(lean_object* v_u_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v___x_679_; lean_object* v_mctx_680_; uint8_t v___x_681_; lean_object* v___x_682_; 
v___x_679_ = lean_st_ref_get(v_a_675_);
v_mctx_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc_ref(v_mctx_680_);
lean_dec(v___x_679_);
v___x_681_ = 1;
v___x_682_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(v_u_673_, v___x_681_, v_a_674_, v_a_675_, v_a_676_, v_a_677_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
if (lean_obj_tag(v_a_683_) == 0)
{
lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_704_; 
lean_inc(v_a_683_);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; 
v_unused_705_ = lean_ctor_get(v___x_682_, 0);
lean_dec(v_unused_705_);
v___x_685_ = v___x_682_;
v_isShared_686_ = v_isSharedCheck_704_;
goto v_resetjp_684_;
}
else
{
lean_dec(v___x_682_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_704_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v_cache_688_; lean_object* v_zetaDeltaFVarIds_689_; lean_object* v_postponed_690_; lean_object* v_diag_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_702_; 
v___x_687_ = lean_st_ref_take(v_a_675_);
v_cache_688_ = lean_ctor_get(v___x_687_, 1);
v_zetaDeltaFVarIds_689_ = lean_ctor_get(v___x_687_, 2);
v_postponed_690_ = lean_ctor_get(v___x_687_, 3);
v_diag_691_ = lean_ctor_get(v___x_687_, 4);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_702_ == 0)
{
lean_object* v_unused_703_; 
v_unused_703_ = lean_ctor_get(v___x_687_, 0);
lean_dec(v_unused_703_);
v___x_693_ = v___x_687_;
v_isShared_694_ = v_isSharedCheck_702_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_diag_691_);
lean_inc(v_postponed_690_);
lean_inc(v_zetaDeltaFVarIds_689_);
lean_inc(v_cache_688_);
lean_dec(v___x_687_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_702_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v_mctx_680_);
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_mctx_680_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_cache_688_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_zetaDeltaFVarIds_689_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_postponed_690_);
lean_ctor_set(v_reuseFailAlloc_701_, 4, v_diag_691_);
v___x_696_ = v_reuseFailAlloc_701_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = lean_st_ref_put(v_a_675_, v___x_696_);
if (v_isShared_686_ == 0)
{
v___x_699_ = v___x_685_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_683_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
else
{
lean_dec_ref(v_mctx_680_);
return v___x_682_;
}
}
else
{
lean_dec_ref(v_mctx_680_);
return v___x_682_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_decLevel_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_673_ = stack[0].m_obj;
lean_object* v_a_674_ = stack[1].m_obj;
lean_object* v_a_675_ = stack[2].m_obj;
lean_object* v_a_676_ = stack[3].m_obj;
lean_object* v_a_677_ = stack[4].m_obj;
lean_object* v_res_706_;
v_res_706_ = l_Lean_Meta_decLevel_x3f(v_u_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_);
stack->m_obj
 = v_res_706_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel_x3f___boxed(lean_object* v_u_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_Meta_decLevel_x3f(v_u_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
return v_res_713_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(lean_object* v_msg_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_ref_720_; lean_object* v___x_721_; lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_730_; 
v_ref_720_ = lean_ctor_get(v___y_717_, 2);
v___x_721_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4(v_msg_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
v_a_722_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_730_ == 0)
{
v___x_724_ = v___x_721_;
v_isShared_725_ = v_isSharedCheck_730_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_730_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v___x_728_; 
lean_inc(v_ref_720_);
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v_ref_720_);
lean_ctor_set(v___x_726_, 1, v_a_722_);
if (v_isShared_725_ == 0)
{
lean_ctor_set_tag(v___x_724_, 1);
lean_ctor_set(v___x_724_, 0, v___x_726_);
v___x_728_ = v___x_724_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_714_ = stack[0].m_obj;
lean_object* v___y_715_ = stack[1].m_obj;
lean_object* v___y_716_ = stack[2].m_obj;
lean_object* v___y_717_ = stack[3].m_obj;
lean_object* v___y_718_ = stack[4].m_obj;
lean_object* v_res_731_;
v_res_731_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(v_msg_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
stack->m_obj
 = v_res_731_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg___boxed(lean_object* v_msg_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(v_msg_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
return v_res_738_;
}
}
static lean_object* _init_l_Lean_Meta_decLevel___closed__1(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = ((lean_object*)(l_Lean_Meta_decLevel___closed__0));
v___x_741_ = l_Lean_stringToMessageData(v___x_740_);
return v___x_741_;
}
}
static lean_object* _init_l_Lean_Meta_decLevel___closed__3(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = ((lean_object*)(l_Lean_Meta_decLevel___closed__2));
v___x_744_ = l_Lean_stringToMessageData(v___x_743_);
return v___x_744_;
}
}
lean_object* l_Lean_Meta_decLevel(lean_object* v_u_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v___x_751_; 
lean_inc(v_u_745_);
v___x_751_ = l_Lean_Meta_decLevel_x3f(v_u_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_766_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_766_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_766_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_766_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
if (lean_obj_tag(v_a_752_) == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
lean_del_object(v___x_754_);
v___x_756_ = lean_obj_once(&l_Lean_Meta_decLevel___closed__1, &l_Lean_Meta_decLevel___closed__1_once, _init_l_Lean_Meta_decLevel___closed__1);
v___x_757_ = l_Lean_MessageData_ofLevel(v_u_745_);
v___x_758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_756_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = lean_obj_once(&l_Lean_Meta_decLevel___closed__3, &l_Lean_Meta_decLevel___closed__3_once, _init_l_Lean_Meta_decLevel___closed__3);
v___x_760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_758_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(v___x_760_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
return v___x_761_;
}
else
{
lean_object* v_val_762_; lean_object* v___x_764_; 
lean_dec(v_u_745_);
v_val_762_ = lean_ctor_get(v_a_752_, 0);
lean_inc(v_val_762_);
lean_dec_ref_known(v_a_752_, 1);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v_val_762_);
v___x_764_ = v___x_754_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_val_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec(v_u_745_);
v_a_767_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_751_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_751_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_decLevel_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_745_ = stack[0].m_obj;
lean_object* v_a_746_ = stack[1].m_obj;
lean_object* v_a_747_ = stack[2].m_obj;
lean_object* v_a_748_ = stack[3].m_obj;
lean_object* v_a_749_ = stack[4].m_obj;
lean_object* v_res_775_;
v_res_775_ = l_Lean_Meta_decLevel(v_u_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
stack->m_obj
 = v_res_775_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel___boxed(lean_object* v_u_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Meta_decLevel(v_u_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
return v_res_782_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0(lean_object* v_00_u03b1_783_, lean_object* v_msg_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(v_msg_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
return v___x_790_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_784_ = stack[1].m_obj;
lean_object* v___y_785_ = stack[2].m_obj;
lean_object* v___y_786_ = stack[3].m_obj;
lean_object* v___y_787_ = stack[4].m_obj;
lean_object* v___y_788_ = stack[5].m_obj;
lean_object* v_res_791_;
v_res_791_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0(lean_box(0), v_msg_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
stack->m_obj
 = v_res_791_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___boxed(lean_object* v_00_u03b1_792_, lean_object* v_msg_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0(v_00_u03b1_792_, v_msg_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
return v_res_799_;
}
}
lean_object* l_Lean_Meta_getDecLevel(lean_object* v_type_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_Meta_getLevel(v_type_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v___x_808_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
lean_dec_ref_known(v___x_806_, 1);
v___x_808_ = l_Lean_Meta_normalizeLevel(v_a_807_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_810_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_808_, 1);
v___x_810_ = l_Lean_Meta_decLevel(v_a_809_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
return v___x_810_;
}
else
{
return v___x_808_;
}
}
else
{
return v___x_806_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_getDecLevel_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_800_ = stack[0].m_obj;
lean_object* v_a_801_ = stack[1].m_obj;
lean_object* v_a_802_ = stack[2].m_obj;
lean_object* v_a_803_ = stack[3].m_obj;
lean_object* v_a_804_ = stack[4].m_obj;
lean_object* v_res_811_;
v_res_811_ = l_Lean_Meta_getDecLevel(v_type_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
stack->m_obj
 = v_res_811_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel___boxed(lean_object* v_type_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_Meta_getDecLevel(v_type_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
return v_res_818_;
}
}
lean_object* l_Lean_Meta_getDecLevel_x3f(lean_object* v_type_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_Meta_getLevel(v_type_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_827_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_826_);
lean_dec_ref_known(v___x_825_, 1);
v___x_827_ = l_Lean_Meta_normalizeLevel(v_a_826_, v_a_820_, v_a_821_, v_a_822_, v_a_823_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_829_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref_known(v___x_827_, 1);
v___x_829_ = l_Lean_Meta_decLevel_x3f(v_a_828_, v_a_820_, v_a_821_, v_a_822_, v_a_823_);
return v___x_829_;
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
v_a_830_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_827_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_827_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
v_a_838_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_825_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_825_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_getDecLevel_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_819_ = stack[0].m_obj;
lean_object* v_a_820_ = stack[1].m_obj;
lean_object* v_a_821_ = stack[2].m_obj;
lean_object* v_a_822_ = stack[3].m_obj;
lean_object* v_a_823_ = stack[4].m_obj;
lean_object* v_res_846_;
v_res_846_ = l_Lean_Meta_getDecLevel_x3f(v_type_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_);
stack->m_obj
 = v_res_846_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel_x3f___boxed(lean_object* v_type_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_Meta_getDecLevel_x3f(v_type_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
return v_res_853_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_895_ = lean_unsigned_to_nat(3263537904u);
v___x_896_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_));
v___x_897_ = l_Lean_Name_num___override(v___x_896_, v___x_895_);
return v___x_897_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_899_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_));
v___x_900_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_);
v___x_901_ = l_Lean_Name_str___override(v___x_900_, v___x_899_);
return v___x_901_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_));
v___x_904_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_);
v___x_905_ = l_Lean_Name_str___override(v___x_904_, v___x_903_);
return v___x_905_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_906_ = lean_unsigned_to_nat(2u);
v___x_907_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_);
v___x_908_ = l_Lean_Name_num___override(v___x_907_, v___x_906_);
return v___x_908_;
}
}
lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_910_; uint8_t v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_910_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3));
v___x_911_ = 0;
v___x_912_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_);
v___x_913_ = l_Lean_registerTraceClass(v___x_910_, v___x_911_, v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_914_;
v_res_914_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_();
stack->m_obj
 = v_res_914_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2____boxed(lean_object* v_a_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_();
return v_res_916_;
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
