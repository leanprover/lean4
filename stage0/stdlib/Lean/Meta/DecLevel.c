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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLevelMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_instHashableLevelMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__2;
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
lean_object* v___f_9_; lean_object* v___f_10_; lean_object* v___x_7828__overap_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___f_9_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3___closed__0));
v___f_10_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_10_, 0, v___f_9_);
v___x_7828__overap_11_ = lean_panic_fn_borrowed(v___f_10_, v_msg_2_);
lean_dec_ref(v___f_10_);
v___x_12_ = lean_box(v___y_3_);
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_5_);
lean_inc_ref(v___y_4_);
v___x_13_ = lean_apply_6(v___x_7828__overap_11_, v___x_12_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3___boxed(lean_object* v_msg_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_){
_start:
{
uint8_t v___y_8693__boxed_21_; lean_object* v_res_22_; 
v___y_8693__boxed_21_ = lean_unbox(v___y_15_);
v_res_22_ = l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3(v_msg_14_, v___y_8693__boxed_21_, v___y_16_, v___y_17_, v___y_18_, v___y_19_);
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
v___x_94_ = lean_st_ref_set(v___y_55_, v___x_93_);
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0(void){
_start:
{
size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; 
v___x_147_ = ((size_t)5ULL);
v___x_148_ = ((size_t)1ULL);
v___x_149_ = lean_usize_shift_left(v___x_148_, v___x_147_);
return v___x_149_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_150_; size_t v___x_151_; size_t v___x_152_; 
v___x_150_ = ((size_t)1ULL);
v___x_151_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_152_ = lean_usize_sub(v___x_151_, v___x_150_);
return v___x_152_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(lean_object* v_x_154_, size_t v_x_155_, size_t v_x_156_, lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
if (lean_obj_tag(v_x_154_) == 0)
{
lean_object* v_es_159_; size_t v___x_160_; size_t v___x_161_; size_t v___x_162_; size_t v___x_163_; lean_object* v_j_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v_es_159_ = lean_ctor_get(v_x_154_, 0);
v___x_160_ = ((size_t)5ULL);
v___x_161_ = ((size_t)1ULL);
v___x_162_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_163_ = lean_usize_land(v_x_155_, v___x_162_);
v_j_164_ = lean_usize_to_nat(v___x_163_);
v___x_165_ = lean_array_get_size(v_es_159_);
v___x_166_ = lean_nat_dec_lt(v_j_164_, v___x_165_);
if (v___x_166_ == 0)
{
lean_dec(v_j_164_);
lean_dec(v_x_158_);
lean_dec(v_x_157_);
return v_x_154_;
}
else
{
lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_203_; 
lean_inc_ref(v_es_159_);
v_isSharedCheck_203_ = !lean_is_exclusive(v_x_154_);
if (v_isSharedCheck_203_ == 0)
{
lean_object* v_unused_204_; 
v_unused_204_ = lean_ctor_get(v_x_154_, 0);
lean_dec(v_unused_204_);
v___x_168_ = v_x_154_;
v_isShared_169_ = v_isSharedCheck_203_;
goto v_resetjp_167_;
}
else
{
lean_dec(v_x_154_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_203_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v_v_170_; lean_object* v___x_171_; lean_object* v_xs_x27_172_; lean_object* v___y_174_; 
v_v_170_ = lean_array_fget(v_es_159_, v_j_164_);
v___x_171_ = lean_box(0);
v_xs_x27_172_ = lean_array_fset(v_es_159_, v_j_164_, v___x_171_);
switch(lean_obj_tag(v_v_170_))
{
case 0:
{
lean_object* v_key_179_; lean_object* v_val_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_190_; 
v_key_179_ = lean_ctor_get(v_v_170_, 0);
v_val_180_ = lean_ctor_get(v_v_170_, 1);
v_isSharedCheck_190_ = !lean_is_exclusive(v_v_170_);
if (v_isSharedCheck_190_ == 0)
{
v___x_182_ = v_v_170_;
v_isShared_183_ = v_isSharedCheck_190_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_val_180_);
lean_inc(v_key_179_);
lean_dec(v_v_170_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_190_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
uint8_t v___x_184_; 
v___x_184_ = l_Lean_instBEqLevelMVarId_beq(v_x_157_, v_key_179_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; lean_object* v___x_186_; 
lean_del_object(v___x_182_);
v___x_185_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_179_, v_val_180_, v_x_157_, v_x_158_);
v___x_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
v___y_174_ = v___x_186_;
goto v___jp_173_;
}
else
{
lean_object* v___x_188_; 
lean_dec(v_val_180_);
lean_dec(v_key_179_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 1, v_x_158_);
lean_ctor_set(v___x_182_, 0, v_x_157_);
v___x_188_ = v___x_182_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_x_157_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_x_158_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
v___y_174_ = v___x_188_;
goto v___jp_173_;
}
}
}
}
case 1:
{
lean_object* v_node_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_201_; 
v_node_191_ = lean_ctor_get(v_v_170_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v_v_170_);
if (v_isSharedCheck_201_ == 0)
{
v___x_193_ = v_v_170_;
v_isShared_194_ = v_isSharedCheck_201_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_node_191_);
lean_dec(v_v_170_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_201_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
size_t v___x_195_; size_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_195_ = lean_usize_shift_right(v_x_155_, v___x_160_);
v___x_196_ = lean_usize_add(v_x_156_, v___x_161_);
v___x_197_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_node_191_, v___x_195_, v___x_196_, v_x_157_, v_x_158_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v___x_197_);
v___x_199_ = v___x_193_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_197_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
v___y_174_ = v___x_199_;
goto v___jp_173_;
}
}
}
default: 
{
lean_object* v___x_202_; 
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v_x_157_);
lean_ctor_set(v___x_202_, 1, v_x_158_);
v___y_174_ = v___x_202_;
goto v___jp_173_;
}
}
v___jp_173_:
{
lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_175_ = lean_array_fset(v_xs_x27_172_, v_j_164_, v___y_174_);
lean_dec(v_j_164_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_175_);
v___x_177_ = v___x_168_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
else
{
lean_object* v_ks_205_; lean_object* v_vs_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_226_; 
v_ks_205_ = lean_ctor_get(v_x_154_, 0);
v_vs_206_ = lean_ctor_get(v_x_154_, 1);
v_isSharedCheck_226_ = !lean_is_exclusive(v_x_154_);
if (v_isSharedCheck_226_ == 0)
{
v___x_208_ = v_x_154_;
v_isShared_209_ = v_isSharedCheck_226_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_vs_206_);
lean_inc(v_ks_205_);
lean_dec(v_x_154_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_226_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_ks_205_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_vs_206_);
v___x_211_ = v_reuseFailAlloc_225_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v_newNode_212_; uint8_t v___y_214_; size_t v___x_220_; uint8_t v___x_221_; 
v_newNode_212_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8___redArg(v___x_211_, v_x_157_, v_x_158_);
v___x_220_ = ((size_t)7ULL);
v___x_221_ = lean_usize_dec_le(v___x_220_, v_x_156_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_222_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_212_);
v___x_223_ = lean_unsigned_to_nat(4u);
v___x_224_ = lean_nat_dec_lt(v___x_222_, v___x_223_);
lean_dec(v___x_222_);
v___y_214_ = v___x_224_;
goto v___jp_213_;
}
else
{
v___y_214_ = v___x_221_;
goto v___jp_213_;
}
v___jp_213_:
{
if (v___y_214_ == 0)
{
lean_object* v_ks_215_; lean_object* v_vs_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_ks_215_ = lean_ctor_get(v_newNode_212_, 0);
lean_inc_ref(v_ks_215_);
v_vs_216_ = lean_ctor_get(v_newNode_212_, 1);
lean_inc_ref(v_vs_216_);
lean_dec_ref(v_newNode_212_);
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__2);
v___x_219_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(v_x_156_, v_ks_215_, v_vs_216_, v___x_217_, v___x_218_);
lean_dec_ref(v_vs_216_);
lean_dec_ref(v_ks_215_);
return v___x_219_;
}
else
{
return v_newNode_212_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(size_t v_depth_227_, lean_object* v_keys_228_, lean_object* v_vals_229_, lean_object* v_i_230_, lean_object* v_entries_231_){
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_depth_247_, lean_object* v_keys_248_, lean_object* v_vals_249_, lean_object* v_i_250_, lean_object* v_entries_251_){
_start:
{
size_t v_depth_boxed_252_; lean_object* v_res_253_; 
v_depth_boxed_252_ = lean_unbox_usize(v_depth_247_);
lean_dec(v_depth_247_);
v_res_253_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(v_depth_boxed_252_, v_keys_248_, v_vals_249_, v_i_250_, v_entries_251_);
lean_dec_ref(v_vals_249_);
lean_dec_ref(v_keys_248_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_x_254_, lean_object* v_x_255_, lean_object* v_x_256_, lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
size_t v_x_8935__boxed_259_; size_t v_x_8936__boxed_260_; lean_object* v_res_261_; 
v_x_8935__boxed_259_ = lean_unbox_usize(v_x_255_);
lean_dec(v_x_255_);
v_x_8936__boxed_260_ = lean_unbox_usize(v_x_256_);
lean_dec(v_x_256_);
v_res_261_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_x_254_, v_x_8935__boxed_259_, v_x_8936__boxed_260_, v_x_257_, v_x_258_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2___redArg(lean_object* v_x_262_, lean_object* v_x_263_, lean_object* v_x_264_){
_start:
{
uint64_t v___x_265_; size_t v___x_266_; size_t v___x_267_; lean_object* v___x_268_; 
v___x_265_ = l_Lean_instHashableLevelMVarId_hash(v_x_263_);
v___x_266_ = lean_uint64_to_usize(v___x_265_);
v___x_267_ = ((size_t)1ULL);
v___x_268_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_x_262_, v___x_266_, v___x_267_, v_x_263_, v_x_264_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(lean_object* v_mvarId_269_, lean_object* v_val_270_, lean_object* v___y_271_){
_start:
{
lean_object* v___x_273_; lean_object* v_mctx_274_; lean_object* v_cache_275_; lean_object* v_zetaDeltaFVarIds_276_; lean_object* v_postponed_277_; lean_object* v_diag_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_305_; 
v___x_273_ = lean_st_ref_take(v___y_271_);
v_mctx_274_ = lean_ctor_get(v___x_273_, 0);
v_cache_275_ = lean_ctor_get(v___x_273_, 1);
v_zetaDeltaFVarIds_276_ = lean_ctor_get(v___x_273_, 2);
v_postponed_277_ = lean_ctor_get(v___x_273_, 3);
v_diag_278_ = lean_ctor_get(v___x_273_, 4);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_305_ == 0)
{
v___x_280_ = v___x_273_;
v_isShared_281_ = v_isSharedCheck_305_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_diag_278_);
lean_inc(v_postponed_277_);
lean_inc(v_zetaDeltaFVarIds_276_);
lean_inc(v_cache_275_);
lean_inc(v_mctx_274_);
lean_dec(v___x_273_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_305_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v_depth_282_; lean_object* v_levelAssignDepth_283_; lean_object* v_mvarCounter_284_; lean_object* v_lDepth_285_; lean_object* v_decls_286_; lean_object* v_userNames_287_; lean_object* v_lAssignment_288_; lean_object* v_eAssignment_289_; lean_object* v_dAssignment_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_304_; 
v_depth_282_ = lean_ctor_get(v_mctx_274_, 0);
v_levelAssignDepth_283_ = lean_ctor_get(v_mctx_274_, 1);
v_mvarCounter_284_ = lean_ctor_get(v_mctx_274_, 2);
v_lDepth_285_ = lean_ctor_get(v_mctx_274_, 3);
v_decls_286_ = lean_ctor_get(v_mctx_274_, 4);
v_userNames_287_ = lean_ctor_get(v_mctx_274_, 5);
v_lAssignment_288_ = lean_ctor_get(v_mctx_274_, 6);
v_eAssignment_289_ = lean_ctor_get(v_mctx_274_, 7);
v_dAssignment_290_ = lean_ctor_get(v_mctx_274_, 8);
v_isSharedCheck_304_ = !lean_is_exclusive(v_mctx_274_);
if (v_isSharedCheck_304_ == 0)
{
v___x_292_ = v_mctx_274_;
v_isShared_293_ = v_isSharedCheck_304_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_dAssignment_290_);
lean_inc(v_eAssignment_289_);
lean_inc(v_lAssignment_288_);
lean_inc(v_userNames_287_);
lean_inc(v_decls_286_);
lean_inc(v_lDepth_285_);
lean_inc(v_mvarCounter_284_);
lean_inc(v_levelAssignDepth_283_);
lean_inc(v_depth_282_);
lean_dec(v_mctx_274_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_304_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_294_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2___redArg(v_lAssignment_288_, v_mvarId_269_, v_val_270_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 6, v___x_294_);
v___x_296_ = v___x_292_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_depth_282_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_levelAssignDepth_283_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v_mvarCounter_284_);
lean_ctor_set(v_reuseFailAlloc_303_, 3, v_lDepth_285_);
lean_ctor_set(v_reuseFailAlloc_303_, 4, v_decls_286_);
lean_ctor_set(v_reuseFailAlloc_303_, 5, v_userNames_287_);
lean_ctor_set(v_reuseFailAlloc_303_, 6, v___x_294_);
lean_ctor_set(v_reuseFailAlloc_303_, 7, v_eAssignment_289_);
lean_ctor_set(v_reuseFailAlloc_303_, 8, v_dAssignment_290_);
v___x_296_ = v_reuseFailAlloc_303_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_298_; 
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_296_);
v___x_298_ = v___x_280_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_cache_275_);
lean_ctor_set(v_reuseFailAlloc_302_, 2, v_zetaDeltaFVarIds_276_);
lean_ctor_set(v_reuseFailAlloc_302_, 3, v_postponed_277_);
lean_ctor_set(v_reuseFailAlloc_302_, 4, v_diag_278_);
v___x_298_ = v_reuseFailAlloc_302_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = lean_st_ref_set(v___y_271_, v___x_298_);
v___x_300_ = lean_box(0);
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_306_, lean_object* v_val_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(v_mvarId_306_, v_val_307_, v___y_308_);
lean_dec(v___y_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_311_, lean_object* v_vals_312_, lean_object* v_i_313_, lean_object* v_k_314_){
_start:
{
lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_315_ = lean_array_get_size(v_keys_311_);
v___x_316_ = lean_nat_dec_lt(v_i_313_, v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; 
lean_dec(v_i_313_);
v___x_317_ = lean_box(0);
return v___x_317_;
}
else
{
lean_object* v_k_x27_318_; uint8_t v___x_319_; 
v_k_x27_318_ = lean_array_fget_borrowed(v_keys_311_, v_i_313_);
v___x_319_ = l_Lean_instBEqLevelMVarId_beq(v_k_314_, v_k_x27_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_unsigned_to_nat(1u);
v___x_321_ = lean_nat_add(v_i_313_, v___x_320_);
lean_dec(v_i_313_);
v_i_313_ = v___x_321_;
goto _start;
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_array_fget_borrowed(v_vals_312_, v_i_313_);
lean_dec(v_i_313_);
lean_inc(v___x_323_);
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
return v___x_324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_325_, lean_object* v_vals_326_, lean_object* v_i_327_, lean_object* v_k_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg(v_keys_325_, v_vals_326_, v_i_327_, v_k_328_);
lean_dec(v_k_328_);
lean_dec_ref(v_vals_326_);
lean_dec_ref(v_keys_325_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(lean_object* v_x_330_, size_t v_x_331_, lean_object* v_x_332_){
_start:
{
if (lean_obj_tag(v_x_330_) == 0)
{
lean_object* v_es_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_354_; 
v_es_333_ = lean_ctor_get(v_x_330_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v_x_330_);
if (v_isSharedCheck_354_ == 0)
{
v___x_335_ = v_x_330_;
v_isShared_336_ = v_isSharedCheck_354_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_es_333_);
lean_dec(v_x_330_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_354_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; size_t v___x_338_; size_t v___x_339_; size_t v___x_340_; lean_object* v_j_341_; lean_object* v___x_342_; 
v___x_337_ = lean_box(2);
v___x_338_ = ((size_t)5ULL);
v___x_339_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__1);
v___x_340_ = lean_usize_land(v_x_331_, v___x_339_);
v_j_341_ = lean_usize_to_nat(v___x_340_);
v___x_342_ = lean_array_get(v___x_337_, v_es_333_, v_j_341_);
lean_dec(v_j_341_);
lean_dec_ref(v_es_333_);
switch(lean_obj_tag(v___x_342_))
{
case 0:
{
lean_object* v_key_343_; lean_object* v_val_344_; uint8_t v___x_345_; 
v_key_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_key_343_);
v_val_344_ = lean_ctor_get(v___x_342_, 1);
lean_inc(v_val_344_);
lean_dec_ref(v___x_342_);
v___x_345_ = l_Lean_instBEqLevelMVarId_beq(v_x_332_, v_key_343_);
lean_dec(v_key_343_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; 
lean_dec(v_val_344_);
lean_del_object(v___x_335_);
v___x_346_ = lean_box(0);
return v___x_346_;
}
else
{
lean_object* v___x_348_; 
if (v_isShared_336_ == 0)
{
lean_ctor_set_tag(v___x_335_, 1);
lean_ctor_set(v___x_335_, 0, v_val_344_);
v___x_348_ = v___x_335_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_val_344_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
case 1:
{
lean_object* v_node_350_; size_t v___x_351_; 
lean_del_object(v___x_335_);
v_node_350_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_node_350_);
lean_dec_ref(v___x_342_);
v___x_351_ = lean_usize_shift_right(v_x_331_, v___x_338_);
v_x_330_ = v_node_350_;
v_x_331_ = v___x_351_;
goto _start;
}
default: 
{
lean_object* v___x_353_; 
lean_del_object(v___x_335_);
v___x_353_ = lean_box(0);
return v___x_353_;
}
}
}
}
else
{
lean_object* v_ks_355_; lean_object* v_vs_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v_ks_355_ = lean_ctor_get(v_x_330_, 0);
lean_inc_ref(v_ks_355_);
v_vs_356_ = lean_ctor_get(v_x_330_, 1);
lean_inc_ref(v_vs_356_);
lean_dec_ref(v_x_330_);
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg(v_ks_355_, v_vs_356_, v___x_357_, v_x_332_);
lean_dec_ref(v_vs_356_);
lean_dec_ref(v_ks_355_);
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_359_, lean_object* v_x_360_, lean_object* v_x_361_){
_start:
{
size_t v_x_9179__boxed_362_; lean_object* v_res_363_; 
v_x_9179__boxed_362_ = lean_unbox_usize(v_x_360_);
lean_dec(v_x_360_);
v_res_363_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(v_x_359_, v_x_9179__boxed_362_, v_x_361_);
lean_dec(v_x_361_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(lean_object* v_x_400_, uint8_t v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v_u_411_; lean_object* v_v_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; 
switch(lean_obj_tag(v_x_400_))
{
case 0:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_box(0);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
return v___x_440_;
}
case 4:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec_ref(v_x_400_);
v___x_441_ = lean_box(0);
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
return v___x_442_;
}
case 5:
{
lean_object* v_a_443_; lean_object* v___x_444_; lean_object* v_mctx_445_; lean_object* v_lAssignment_446_; lean_object* v___x_447_; 
v_a_443_ = lean_ctor_get(v_x_400_, 0);
lean_inc(v_a_443_);
lean_dec_ref(v_x_400_);
v___x_444_ = lean_st_ref_get(v_a_403_);
v_mctx_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc_ref(v_mctx_445_);
lean_dec(v___x_444_);
v_lAssignment_446_ = lean_ctor_get(v_mctx_445_, 6);
lean_inc_ref(v_lAssignment_446_);
lean_dec_ref(v_mctx_445_);
v___x_447_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg(v_lAssignment_446_, v_a_443_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v___x_448_; 
lean_inc(v_a_443_);
v___x_448_ = l_Lean_LMVarId_isReadOnly(v_a_443_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_519_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_519_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_519_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_519_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
uint8_t v___x_453_; 
v___x_453_ = lean_unbox(v_a_449_);
lean_dec(v_a_449_);
if (v___x_453_ == 0)
{
if (v_a_401_ == 0)
{
lean_object* v___x_455_; 
lean_dec(v_a_443_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_447_);
v___x_455_ = v___x_451_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_447_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
else
{
lean_object* v___x_457_; 
lean_del_object(v___x_451_);
v___x_457_ = l_Lean_Meta_mkFreshLevelMVar(v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; uint8_t v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v_options_484_; uint8_t v_hasTrace_485_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref(v___x_457_);
v_options_484_ = lean_ctor_get(v_a_404_, 2);
v_hasTrace_485_ = lean_ctor_get_uint8(v_options_484_, sizeof(void*)*1);
if (v_hasTrace_485_ == 0)
{
v___y_460_ = v_a_401_;
v___y_461_ = v_a_402_;
v___y_462_ = v_a_403_;
v___y_463_ = v_a_404_;
v___y_464_ = v_a_405_;
goto v___jp_459_;
}
else
{
lean_object* v_inheritedTraceOptions_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_inheritedTraceOptions_486_ = lean_ctor_get(v_a_404_, 13);
v___x_487_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3));
v___x_488_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6_once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6);
v___x_489_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_486_, v_options_484_, v___x_488_);
if (v___x_489_ == 0)
{
v___y_460_ = v_a_401_;
v___y_461_ = v_a_402_;
v___y_462_ = v_a_403_;
v___y_463_ = v_a_404_;
v___y_464_ = v_a_405_;
goto v___jp_459_;
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_490_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8_once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8);
lean_inc(v_a_443_);
v___x_491_ = l_Lean_mkLevelMVar(v_a_443_);
v___x_492_ = l_Lean_MessageData_ofLevel(v___x_491_);
v___x_493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_490_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10_once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10);
v___x_495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_493_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
lean_inc(v_a_458_);
v___x_496_ = l_Lean_Level_succ___override(v_a_458_);
v___x_497_ = l_Lean_MessageData_ofLevel(v___x_496_);
v___x_498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_495_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg(v___x_487_, v___x_498_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_dec_ref(v___x_499_);
v___y_460_ = v_a_401_;
v___y_461_ = v_a_402_;
v___y_462_ = v_a_403_;
v___y_463_ = v_a_404_;
v___y_464_ = v_a_405_;
goto v___jp_459_;
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_dec(v_a_458_);
lean_dec(v_a_443_);
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
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
}
v___jp_459_:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
lean_inc(v_a_458_);
v___x_465_ = l_Lean_Level_succ___override(v_a_458_);
v___x_466_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(v_a_443_, v___x_465_, v___y_462_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_474_; 
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; 
v_unused_475_ = lean_ctor_get(v___x_466_, 0);
lean_dec(v_unused_475_);
v___x_468_ = v___x_466_;
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
else
{
lean_dec(v___x_466_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_470_, 0, v_a_458_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_470_);
v___x_472_ = v___x_468_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec(v_a_458_);
v_a_476_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_466_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_466_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec(v_a_443_);
v_a_508_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_457_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_457_);
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
}
else
{
lean_object* v___x_517_; 
lean_dec(v_a_443_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_447_);
v___x_517_ = v___x_451_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_447_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_dec(v_a_443_);
v_a_520_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_448_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_448_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
else
{
lean_object* v_val_528_; 
lean_dec(v_a_443_);
v_val_528_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_val_528_);
lean_dec_ref(v___x_447_);
v_x_400_ = v_val_528_;
goto _start;
}
}
case 1:
{
lean_object* v_a_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_a_530_ = lean_ctor_get(v_x_400_, 0);
lean_inc(v_a_530_);
lean_dec_ref(v_x_400_);
v___x_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_531_, 0, v_a_530_);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
default: 
{
switch(lean_obj_tag(v_x_400_))
{
case 2:
{
lean_object* v_a_533_; lean_object* v_a_534_; 
v_a_533_ = lean_ctor_get(v_x_400_, 0);
lean_inc(v_a_533_);
v_a_534_ = lean_ctor_get(v_x_400_, 1);
lean_inc(v_a_534_);
lean_dec_ref(v_x_400_);
v_u_411_ = v_a_533_;
v_v_412_ = v_a_534_;
v___y_413_ = v_a_402_;
v___y_414_ = v_a_403_;
v___y_415_ = v_a_404_;
v___y_416_ = v_a_405_;
goto v___jp_410_;
}
case 3:
{
lean_object* v_a_535_; lean_object* v_a_536_; 
v_a_535_ = lean_ctor_get(v_x_400_, 0);
lean_inc(v_a_535_);
v_a_536_ = lean_ctor_get(v_x_400_, 1);
lean_inc(v_a_536_);
lean_dec_ref(v_x_400_);
v_u_411_ = v_a_535_;
v_v_412_ = v_a_536_;
v___y_413_ = v_a_402_;
v___y_414_ = v_a_403_;
v___y_415_ = v_a_404_;
v___y_416_ = v_a_405_;
goto v___jp_410_;
}
default: 
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec(v_x_400_);
v___x_537_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14_once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14);
v___x_538_ = l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3(v___x_537_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
return v___x_538_;
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
lean_dec_ref(v___x_418_);
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
lean_dec_ref(v_a_419_);
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
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1(lean_object* v_mvarId_556_, lean_object* v_val_557_, uint8_t v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(v_mvarId_556_, v_val_557_, v___y_560_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___boxed(lean_object* v_mvarId_565_, lean_object* v_val_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
uint8_t v___y_9604__boxed_573_; lean_object* v_res_574_; 
v___y_9604__boxed_573_ = lean_unbox(v___y_567_);
v_res_574_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1(v_mvarId_565_, v_val_566_, v___y_9604__boxed_573_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2(lean_object* v_cls_575_, lean_object* v_msg_576_, uint8_t v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg(v_cls_575_, v_msg_576_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___boxed(lean_object* v_cls_584_, lean_object* v_msg_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
uint8_t v___y_9624__boxed_592_; lean_object* v_res_593_; 
v___y_9624__boxed_592_ = lean_unbox(v___y_586_);
v_res_593_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2(v_cls_584_, v_msg_585_, v___y_9624__boxed_592_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0(lean_object* v_00_u03b2_594_, lean_object* v_x_595_, size_t v_x_596_, lean_object* v_x_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(v_x_595_, v_x_596_, v_x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_599_, lean_object* v_x_600_, lean_object* v_x_601_, lean_object* v_x_602_){
_start:
{
size_t v_x_9645__boxed_603_; lean_object* v_res_604_; 
v_x_9645__boxed_603_ = lean_unbox_usize(v_x_601_);
lean_dec(v_x_601_);
v_res_604_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0(v_00_u03b2_599_, v_x_600_, v_x_9645__boxed_603_, v_x_602_);
lean_dec(v_x_602_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2(lean_object* v_00_u03b2_605_, lean_object* v_x_606_, lean_object* v_x_607_, lean_object* v_x_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2___redArg(v_x_606_, v_x_607_, v_x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_610_, lean_object* v_keys_611_, lean_object* v_vals_612_, lean_object* v_heq_613_, lean_object* v_i_614_, lean_object* v_k_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg(v_keys_611_, v_vals_612_, v_i_614_, v_k_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_617_, lean_object* v_keys_618_, lean_object* v_vals_619_, lean_object* v_heq_620_, lean_object* v_i_621_, lean_object* v_k_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2(v_00_u03b2_617_, v_keys_618_, v_vals_619_, v_heq_620_, v_i_621_, v_k_622_);
lean_dec(v_k_622_);
lean_dec_ref(v_vals_619_);
lean_dec_ref(v_keys_618_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_624_, lean_object* v_x_625_, size_t v_x_626_, size_t v_x_627_, lean_object* v_x_628_, lean_object* v_x_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_x_625_, v_x_626_, v_x_627_, v_x_628_, v_x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_631_, lean_object* v_x_632_, lean_object* v_x_633_, lean_object* v_x_634_, lean_object* v_x_635_, lean_object* v_x_636_){
_start:
{
size_t v_x_9666__boxed_637_; size_t v_x_9667__boxed_638_; lean_object* v_res_639_; 
v_x_9666__boxed_637_ = lean_unbox_usize(v_x_633_);
lean_dec(v_x_633_);
v_x_9667__boxed_638_ = lean_unbox_usize(v_x_634_);
lean_dec(v_x_634_);
v_res_639_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5(v_00_u03b2_631_, v_x_632_, v_x_9666__boxed_637_, v_x_9667__boxed_638_, v_x_635_, v_x_636_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_640_, lean_object* v_n_641_, lean_object* v_k_642_, lean_object* v_v_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8___redArg(v_n_641_, v_k_642_, v_v_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_645_, size_t v_depth_646_, lean_object* v_keys_647_, lean_object* v_vals_648_, lean_object* v_heq_649_, lean_object* v_i_650_, lean_object* v_entries_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(v_depth_646_, v_keys_647_, v_vals_648_, v_i_650_, v_entries_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03b2_653_, lean_object* v_depth_654_, lean_object* v_keys_655_, lean_object* v_vals_656_, lean_object* v_heq_657_, lean_object* v_i_658_, lean_object* v_entries_659_){
_start:
{
size_t v_depth_boxed_660_; lean_object* v_res_661_; 
v_depth_boxed_660_ = lean_unbox_usize(v_depth_654_);
lean_dec(v_depth_654_);
v_res_661_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9(v_00_u03b2_653_, v_depth_boxed_660_, v_keys_655_, v_vals_656_, v_heq_657_, v_i_658_, v_entries_659_);
lean_dec_ref(v_vals_656_);
lean_dec_ref(v_keys_655_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8_spec__9(lean_object* v_00_u03b2_662_, lean_object* v_x_663_, lean_object* v_x_664_, lean_object* v_x_665_, lean_object* v_x_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8_spec__9___redArg(v_x_663_, v_x_664_, v_x_665_, v_x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel_x3f(lean_object* v_u_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v___x_674_; uint8_t v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_st_ref_get(v_a_670_);
v___x_675_ = 1;
v___x_676_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(v_u_668_, v___x_675_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
if (lean_obj_tag(v_a_677_) == 0)
{
lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_699_; 
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; 
v_unused_700_ = lean_ctor_get(v___x_676_, 0);
lean_dec(v_unused_700_);
v___x_679_ = v___x_676_;
v_isShared_680_ = v_isSharedCheck_699_;
goto v_resetjp_678_;
}
else
{
lean_dec(v___x_676_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_699_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; lean_object* v_mctx_682_; lean_object* v_cache_683_; lean_object* v_zetaDeltaFVarIds_684_; lean_object* v_postponed_685_; lean_object* v_diag_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_697_; 
v___x_681_ = lean_st_ref_take(v_a_670_);
v_mctx_682_ = lean_ctor_get(v___x_674_, 0);
lean_inc_ref(v_mctx_682_);
lean_dec(v___x_674_);
v_cache_683_ = lean_ctor_get(v___x_681_, 1);
v_zetaDeltaFVarIds_684_ = lean_ctor_get(v___x_681_, 2);
v_postponed_685_ = lean_ctor_get(v___x_681_, 3);
v_diag_686_ = lean_ctor_get(v___x_681_, 4);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; 
v_unused_698_ = lean_ctor_get(v___x_681_, 0);
lean_dec(v_unused_698_);
v___x_688_ = v___x_681_;
v_isShared_689_ = v_isSharedCheck_697_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_diag_686_);
lean_inc(v_postponed_685_);
lean_inc(v_zetaDeltaFVarIds_684_);
lean_inc(v_cache_683_);
lean_dec(v___x_681_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_697_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v_mctx_682_);
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_mctx_682_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_cache_683_);
lean_ctor_set(v_reuseFailAlloc_696_, 2, v_zetaDeltaFVarIds_684_);
lean_ctor_set(v_reuseFailAlloc_696_, 3, v_postponed_685_);
lean_ctor_set(v_reuseFailAlloc_696_, 4, v_diag_686_);
v___x_691_ = v_reuseFailAlloc_696_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_692_ = lean_st_ref_set(v_a_670_, v___x_691_);
if (v_isShared_680_ == 0)
{
v___x_694_ = v___x_679_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_677_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_677_);
lean_dec(v___x_674_);
return v___x_676_;
}
}
else
{
lean_dec(v___x_674_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel_x3f___boxed(lean_object* v_u_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_Meta_decLevel_x3f(v_u_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(lean_object* v_msg_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_ref_714_; lean_object* v___x_715_; lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_724_; 
v_ref_714_ = lean_ctor_get(v___y_711_, 5);
v___x_715_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4(v_msg_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
v_a_716_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_724_ == 0)
{
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_724_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_724_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_722_; 
lean_inc(v_ref_714_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v_ref_714_);
lean_ctor_set(v___x_720_, 1, v_a_716_);
if (v_isShared_719_ == 0)
{
lean_ctor_set_tag(v___x_718_, 1);
lean_ctor_set(v___x_718_, 0, v___x_720_);
v___x_722_ = v___x_718_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg___boxed(lean_object* v_msg_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(v_msg_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
return v_res_731_;
}
}
static lean_object* _init_l_Lean_Meta_decLevel___closed__1(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = ((lean_object*)(l_Lean_Meta_decLevel___closed__0));
v___x_734_ = l_Lean_stringToMessageData(v___x_733_);
return v___x_734_;
}
}
static lean_object* _init_l_Lean_Meta_decLevel___closed__3(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = ((lean_object*)(l_Lean_Meta_decLevel___closed__2));
v___x_737_ = l_Lean_stringToMessageData(v___x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel(lean_object* v_u_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v___x_744_; 
lean_inc(v_u_738_);
v___x_744_ = l_Lean_Meta_decLevel_x3f(v_u_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_759_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_759_ == 0)
{
v___x_747_ = v___x_744_;
v_isShared_748_ = v_isSharedCheck_759_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_759_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
if (lean_obj_tag(v_a_745_) == 0)
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
lean_del_object(v___x_747_);
v___x_749_ = lean_obj_once(&l_Lean_Meta_decLevel___closed__1, &l_Lean_Meta_decLevel___closed__1_once, _init_l_Lean_Meta_decLevel___closed__1);
v___x_750_ = l_Lean_MessageData_ofLevel(v_u_738_);
v___x_751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_749_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = lean_obj_once(&l_Lean_Meta_decLevel___closed__3, &l_Lean_Meta_decLevel___closed__3_once, _init_l_Lean_Meta_decLevel___closed__3);
v___x_753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_751_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(v___x_753_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
return v___x_754_;
}
else
{
lean_object* v_val_755_; lean_object* v___x_757_; 
lean_dec(v_u_738_);
v_val_755_ = lean_ctor_get(v_a_745_, 0);
lean_inc(v_val_755_);
lean_dec_ref(v_a_745_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v_val_755_);
v___x_757_ = v___x_747_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_val_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec(v_u_738_);
v_a_760_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_744_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_744_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel___boxed(lean_object* v_u_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_Meta_decLevel(v_u_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0(lean_object* v_00_u03b1_775_, lean_object* v_msg_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(v_msg_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___boxed(lean_object* v_00_u03b1_783_, lean_object* v_msg_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0(v_00_u03b1_783_, v_msg_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel(lean_object* v_type_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_Meta_getLevel(v_type_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_799_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref(v___x_797_);
v___x_799_ = l_Lean_Meta_decLevel(v_a_798_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
return v___x_799_;
}
else
{
return v___x_797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel___boxed(lean_object* v_type_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_Meta_getDecLevel(v_type_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel_x3f(lean_object* v_type_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_Meta_getLevel(v_type_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_815_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
lean_dec_ref(v___x_813_);
v___x_815_ = l_Lean_Meta_decLevel_x3f(v_a_814_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
return v___x_815_;
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
v_a_816_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_813_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_813_);
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_DecLevel(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
