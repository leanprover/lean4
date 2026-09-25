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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3(lean_object* v_msg_2_, uint8_t v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___f_9_; lean_object* v___f_10_; lean_object* v___x_7001__overap_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___f_9_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3___closed__0));
v___f_10_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_10_, 0, v___f_9_);
v___x_7001__overap_11_ = lean_panic_fn_borrowed(v___f_10_, v_msg_2_);
lean_dec_ref(v___f_10_);
v___x_12_ = lean_box(v___y_3_);
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_5_);
lean_inc_ref(v___y_4_);
v___x_13_ = lean_apply_6(v___x_7001__overap_11_, v___x_12_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3___boxed(lean_object* v_msg_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_){
_start:
{
uint8_t v___y_7888__boxed_21_; lean_object* v_res_22_; 
v___y_7888__boxed_21_ = lean_unbox(v___y_15_);
v_res_22_ = l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3(v_msg_14_, v___y_7888__boxed_21_, v___y_16_, v___y_17_, v___y_18_, v___y_19_);
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
lean_object* v___x_29_; lean_object* v_env_30_; lean_object* v___x_31_; lean_object* v_toCold_32_; lean_object* v_mctx_33_; lean_object* v_lctx_34_; lean_object* v_options_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_29_ = lean_st_ref_get(v___y_27_);
v_env_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc_ref(v_env_30_);
lean_dec(v___x_29_);
v___x_31_ = lean_st_ref_get(v___y_25_);
v_toCold_32_ = lean_ctor_get(v___y_26_, 0);
v_mctx_33_ = lean_ctor_get(v___x_31_, 0);
lean_inc_ref(v_mctx_33_);
lean_dec(v___x_31_);
v_lctx_34_ = lean_ctor_get(v___y_24_, 2);
v_options_35_ = lean_ctor_get(v_toCold_32_, 2);
lean_inc_ref(v_options_35_);
lean_inc_ref(v_lctx_34_);
v___x_36_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_36_, 0, v_env_30_);
lean_ctor_set(v___x_36_, 1, v_mctx_33_);
lean_ctor_set(v___x_36_, 2, v_lctx_34_);
lean_ctor_set(v___x_36_, 3, v_options_35_);
v___x_37_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
lean_ctor_set(v___x_37_, 1, v_msgData_23_);
v___x_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4___boxed(lean_object* v_msgData_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4(v_msgData_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_45_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_46_; double v___x_47_; 
v___x_46_ = lean_unsigned_to_nat(0u);
v___x_47_ = lean_float_of_nat(v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg(lean_object* v_cls_51_, lean_object* v_msg_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_ref_58_; lean_object* v___x_59_; lean_object* v_a_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_105_; 
v_ref_58_ = lean_ctor_get(v___y_55_, 2);
v___x_59_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4(v_msg_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
v_a_60_ = lean_ctor_get(v___x_59_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_105_ == 0)
{
v___x_62_ = v___x_59_;
v_isShared_63_ = v_isSharedCheck_105_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_a_60_);
lean_dec(v___x_59_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_105_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_64_; lean_object* v_traceState_65_; lean_object* v_env_66_; lean_object* v_nextMacroScope_67_; lean_object* v_ngen_68_; lean_object* v_auxDeclNGen_69_; lean_object* v_cache_70_; lean_object* v_recordedDeps_71_; lean_object* v_messages_72_; lean_object* v_infoState_73_; lean_object* v_snapshotTasks_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_104_; 
v___x_64_ = lean_st_ref_take(v___y_56_);
v_traceState_65_ = lean_ctor_get(v___x_64_, 4);
v_env_66_ = lean_ctor_get(v___x_64_, 0);
v_nextMacroScope_67_ = lean_ctor_get(v___x_64_, 1);
v_ngen_68_ = lean_ctor_get(v___x_64_, 2);
v_auxDeclNGen_69_ = lean_ctor_get(v___x_64_, 3);
v_cache_70_ = lean_ctor_get(v___x_64_, 5);
v_recordedDeps_71_ = lean_ctor_get(v___x_64_, 6);
v_messages_72_ = lean_ctor_get(v___x_64_, 7);
v_infoState_73_ = lean_ctor_get(v___x_64_, 8);
v_snapshotTasks_74_ = lean_ctor_get(v___x_64_, 9);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_104_ == 0)
{
v___x_76_ = v___x_64_;
v_isShared_77_ = v_isSharedCheck_104_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_snapshotTasks_74_);
lean_inc(v_infoState_73_);
lean_inc(v_messages_72_);
lean_inc(v_recordedDeps_71_);
lean_inc(v_cache_70_);
lean_inc(v_traceState_65_);
lean_inc(v_auxDeclNGen_69_);
lean_inc(v_ngen_68_);
lean_inc(v_nextMacroScope_67_);
lean_inc(v_env_66_);
lean_dec(v___x_64_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_104_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
uint64_t v_tid_78_; lean_object* v_traces_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_103_; 
v_tid_78_ = lean_ctor_get_uint64(v_traceState_65_, sizeof(void*)*1);
v_traces_79_ = lean_ctor_get(v_traceState_65_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v_traceState_65_);
if (v_isSharedCheck_103_ == 0)
{
v___x_81_ = v_traceState_65_;
v_isShared_82_ = v_isSharedCheck_103_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_traces_79_);
lean_dec(v_traceState_65_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_103_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; lean_object* v___x_84_; double v___x_85_; uint8_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_83_ = lean_box(0);
v___x_84_ = lean_box(0);
v___x_85_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__0);
v___x_86_ = 0;
v___x_87_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__1));
v___x_88_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_88_, 0, v_cls_51_);
lean_ctor_set(v___x_88_, 1, v___x_84_);
lean_ctor_set(v___x_88_, 2, v___x_87_);
lean_ctor_set_float(v___x_88_, sizeof(void*)*3, v___x_85_);
lean_ctor_set_float(v___x_88_, sizeof(void*)*3 + 8, v___x_85_);
lean_ctor_set_uint8(v___x_88_, sizeof(void*)*3 + 16, v___x_86_);
v___x_89_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___closed__2));
v___x_90_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_90_, 0, v___x_88_);
lean_ctor_set(v___x_90_, 1, v_a_60_);
lean_ctor_set(v___x_90_, 2, v___x_89_);
lean_inc(v_ref_58_);
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v_ref_58_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = l_Lean_PersistentArray_push___redArg(v_traces_79_, v___x_91_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 0, v___x_92_);
v___x_94_ = v___x_81_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_92_);
lean_ctor_set_uint64(v_reuseFailAlloc_102_, sizeof(void*)*1, v_tid_78_);
v___x_94_ = v_reuseFailAlloc_102_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
lean_object* v___x_96_; 
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 4, v___x_94_);
v___x_96_ = v___x_76_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_env_66_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_nextMacroScope_67_);
lean_ctor_set(v_reuseFailAlloc_101_, 2, v_ngen_68_);
lean_ctor_set(v_reuseFailAlloc_101_, 3, v_auxDeclNGen_69_);
lean_ctor_set(v_reuseFailAlloc_101_, 4, v___x_94_);
lean_ctor_set(v_reuseFailAlloc_101_, 5, v_cache_70_);
lean_ctor_set(v_reuseFailAlloc_101_, 6, v_recordedDeps_71_);
lean_ctor_set(v_reuseFailAlloc_101_, 7, v_messages_72_);
lean_ctor_set(v_reuseFailAlloc_101_, 8, v_infoState_73_);
lean_ctor_set(v_reuseFailAlloc_101_, 9, v_snapshotTasks_74_);
v___x_96_ = v_reuseFailAlloc_101_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
lean_object* v___x_97_; lean_object* v___x_99_; 
v___x_97_ = lean_st_ref_put(v___y_56_, v___x_96_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 0, v___x_83_);
v___x_99_ = v___x_62_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_83_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg___boxed(lean_object* v_cls_106_, lean_object* v_msg_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg(v_cls_106_, v_msg_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8_spec__9___redArg(lean_object* v_x_114_, lean_object* v_x_115_, lean_object* v_x_116_, lean_object* v_x_117_){
_start:
{
lean_object* v_ks_118_; lean_object* v_vs_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_143_; 
v_ks_118_ = lean_ctor_get(v_x_114_, 0);
v_vs_119_ = lean_ctor_get(v_x_114_, 1);
v_isSharedCheck_143_ = !lean_is_exclusive(v_x_114_);
if (v_isSharedCheck_143_ == 0)
{
v___x_121_ = v_x_114_;
v_isShared_122_ = v_isSharedCheck_143_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_vs_119_);
lean_inc(v_ks_118_);
lean_dec(v_x_114_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_143_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = lean_array_get_size(v_ks_118_);
v___x_124_ = lean_nat_dec_lt(v_x_115_, v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_128_; 
lean_dec(v_x_115_);
v___x_125_ = lean_array_push(v_ks_118_, v_x_116_);
v___x_126_ = lean_array_push(v_vs_119_, v_x_117_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v___x_126_);
lean_ctor_set(v___x_121_, 0, v___x_125_);
v___x_128_ = v___x_121_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_125_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
else
{
lean_object* v_k_x27_130_; uint8_t v___x_131_; 
v_k_x27_130_ = lean_array_fget_borrowed(v_ks_118_, v_x_115_);
v___x_131_ = l_Lean_instBEqLevelMVarId_beq(v_x_116_, v_k_x27_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_133_; 
if (v_isShared_122_ == 0)
{
v___x_133_ = v___x_121_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_ks_118_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_vs_119_);
v___x_133_ = v_reuseFailAlloc_137_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_unsigned_to_nat(1u);
v___x_135_ = lean_nat_add(v_x_115_, v___x_134_);
lean_dec(v_x_115_);
v_x_114_ = v___x_133_;
v_x_115_ = v___x_135_;
goto _start;
}
}
else
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_141_; 
v___x_138_ = lean_array_fset(v_ks_118_, v_x_115_, v_x_116_);
v___x_139_ = lean_array_fset(v_vs_119_, v_x_115_, v_x_117_);
lean_dec(v_x_115_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v___x_139_);
lean_ctor_set(v___x_121_, 0, v___x_138_);
v___x_141_ = v___x_121_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_n_144_, lean_object* v_k_145_, lean_object* v_v_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8_spec__9___redArg(v_n_144_, v___x_147_, v_k_145_, v_v_146_);
return v___x_148_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(lean_object* v_x_150_, size_t v_x_151_, size_t v_x_152_, lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
if (lean_obj_tag(v_x_150_) == 0)
{
lean_object* v_es_155_; size_t v___x_156_; size_t v___x_157_; lean_object* v_j_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v_es_155_ = lean_ctor_get(v_x_150_, 0);
v___x_156_ = ((size_t)31ULL);
v___x_157_ = lean_usize_land(v_x_151_, v___x_156_);
v_j_158_ = lean_usize_to_nat(v___x_157_);
v___x_159_ = lean_array_get_size(v_es_155_);
v___x_160_ = lean_nat_dec_lt(v_j_158_, v___x_159_);
if (v___x_160_ == 0)
{
lean_dec(v_j_158_);
lean_dec(v_x_154_);
lean_dec(v_x_153_);
return v_x_150_;
}
else
{
lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_199_; 
lean_inc_ref(v_es_155_);
v_isSharedCheck_199_ = !lean_is_exclusive(v_x_150_);
if (v_isSharedCheck_199_ == 0)
{
lean_object* v_unused_200_; 
v_unused_200_ = lean_ctor_get(v_x_150_, 0);
lean_dec(v_unused_200_);
v___x_162_ = v_x_150_;
v_isShared_163_ = v_isSharedCheck_199_;
goto v_resetjp_161_;
}
else
{
lean_dec(v_x_150_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_199_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v_v_164_; lean_object* v___x_165_; lean_object* v_xs_x27_166_; lean_object* v___y_168_; 
v_v_164_ = lean_array_fget(v_es_155_, v_j_158_);
v___x_165_ = lean_box(0);
v_xs_x27_166_ = lean_array_fset(v_es_155_, v_j_158_, v___x_165_);
switch(lean_obj_tag(v_v_164_))
{
case 0:
{
lean_object* v_key_173_; lean_object* v_val_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_184_; 
v_key_173_ = lean_ctor_get(v_v_164_, 0);
v_val_174_ = lean_ctor_get(v_v_164_, 1);
v_isSharedCheck_184_ = !lean_is_exclusive(v_v_164_);
if (v_isSharedCheck_184_ == 0)
{
v___x_176_ = v_v_164_;
v_isShared_177_ = v_isSharedCheck_184_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_val_174_);
lean_inc(v_key_173_);
lean_dec(v_v_164_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_184_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
uint8_t v___x_178_; 
v___x_178_ = l_Lean_instBEqLevelMVarId_beq(v_x_153_, v_key_173_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_del_object(v___x_176_);
v___x_179_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_173_, v_val_174_, v_x_153_, v_x_154_);
v___x_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
v___y_168_ = v___x_180_;
goto v___jp_167_;
}
else
{
lean_object* v___x_182_; 
lean_dec(v_val_174_);
lean_dec(v_key_173_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 1, v_x_154_);
lean_ctor_set(v___x_176_, 0, v_x_153_);
v___x_182_ = v___x_176_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_x_153_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_x_154_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
v___y_168_ = v___x_182_;
goto v___jp_167_;
}
}
}
}
case 1:
{
lean_object* v_node_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_197_; 
v_node_185_ = lean_ctor_get(v_v_164_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v_v_164_);
if (v_isSharedCheck_197_ == 0)
{
v___x_187_ = v_v_164_;
v_isShared_188_ = v_isSharedCheck_197_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_node_185_);
lean_dec(v_v_164_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_197_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
size_t v___x_189_; size_t v___x_190_; size_t v___x_191_; size_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_189_ = ((size_t)5ULL);
v___x_190_ = lean_usize_shift_right(v_x_151_, v___x_189_);
v___x_191_ = ((size_t)1ULL);
v___x_192_ = lean_usize_add(v_x_152_, v___x_191_);
v___x_193_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_node_185_, v___x_190_, v___x_192_, v_x_153_, v_x_154_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_193_);
v___x_195_ = v___x_187_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
v___y_168_ = v___x_195_;
goto v___jp_167_;
}
}
}
default: 
{
lean_object* v___x_198_; 
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v_x_153_);
lean_ctor_set(v___x_198_, 1, v_x_154_);
v___y_168_ = v___x_198_;
goto v___jp_167_;
}
}
v___jp_167_:
{
lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_169_ = lean_array_fset(v_xs_x27_166_, v_j_158_, v___y_168_);
lean_dec(v_j_158_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_169_);
v___x_171_ = v___x_162_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
else
{
lean_object* v_ks_201_; lean_object* v_vs_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_220_; 
v_ks_201_ = lean_ctor_get(v_x_150_, 0);
v_vs_202_ = lean_ctor_get(v_x_150_, 1);
v_isSharedCheck_220_ = !lean_is_exclusive(v_x_150_);
if (v_isSharedCheck_220_ == 0)
{
v___x_204_ = v_x_150_;
v_isShared_205_ = v_isSharedCheck_220_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_vs_202_);
lean_inc(v_ks_201_);
lean_dec(v_x_150_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_220_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_ks_201_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_vs_202_);
v___x_207_ = v_reuseFailAlloc_219_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v_newNode_208_; size_t v___x_209_; uint8_t v___x_210_; 
v_newNode_208_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8___redArg(v___x_207_, v_x_153_, v_x_154_);
v___x_209_ = ((size_t)7ULL);
v___x_210_ = lean_usize_dec_le(v___x_209_, v_x_152_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_211_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_208_);
v___x_212_ = lean_unsigned_to_nat(4u);
v___x_213_ = lean_nat_dec_lt(v___x_211_, v___x_212_);
lean_dec(v___x_211_);
if (v___x_213_ == 0)
{
lean_object* v_ks_214_; lean_object* v_vs_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_ks_214_ = lean_ctor_get(v_newNode_208_, 0);
lean_inc_ref(v_ks_214_);
v_vs_215_ = lean_ctor_get(v_newNode_208_, 1);
lean_inc_ref(v_vs_215_);
lean_dec_ref(v_newNode_208_);
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_218_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(v_x_152_, v_ks_214_, v_vs_215_, v___x_216_, v___x_217_);
lean_dec_ref(v_vs_215_);
lean_dec_ref(v_ks_214_);
return v___x_218_;
}
else
{
return v_newNode_208_;
}
}
else
{
return v_newNode_208_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(size_t v_depth_221_, lean_object* v_keys_222_, lean_object* v_vals_223_, lean_object* v_i_224_, lean_object* v_entries_225_){
_start:
{
lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_226_ = lean_array_get_size(v_keys_222_);
v___x_227_ = lean_nat_dec_lt(v_i_224_, v___x_226_);
if (v___x_227_ == 0)
{
lean_dec(v_i_224_);
return v_entries_225_;
}
else
{
lean_object* v_k_228_; lean_object* v_v_229_; uint64_t v___x_230_; size_t v_h_231_; size_t v___x_232_; lean_object* v___x_233_; size_t v___x_234_; size_t v___x_235_; size_t v___x_236_; size_t v_h_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v_k_228_ = lean_array_fget_borrowed(v_keys_222_, v_i_224_);
v_v_229_ = lean_array_fget_borrowed(v_vals_223_, v_i_224_);
v___x_230_ = l_Lean_instHashableLevelMVarId_hash(v_k_228_);
v_h_231_ = lean_uint64_to_usize(v___x_230_);
v___x_232_ = ((size_t)5ULL);
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = ((size_t)1ULL);
v___x_235_ = lean_usize_sub(v_depth_221_, v___x_234_);
v___x_236_ = lean_usize_mul(v___x_232_, v___x_235_);
v_h_237_ = lean_usize_shift_right(v_h_231_, v___x_236_);
v___x_238_ = lean_nat_add(v_i_224_, v___x_233_);
lean_dec(v_i_224_);
lean_inc(v_v_229_);
lean_inc(v_k_228_);
v___x_239_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_entries_225_, v_h_237_, v_depth_221_, v_k_228_, v_v_229_);
v_i_224_ = v___x_238_;
v_entries_225_ = v___x_239_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_depth_241_, lean_object* v_keys_242_, lean_object* v_vals_243_, lean_object* v_i_244_, lean_object* v_entries_245_){
_start:
{
size_t v_depth_boxed_246_; lean_object* v_res_247_; 
v_depth_boxed_246_ = lean_unbox_usize(v_depth_241_);
lean_dec(v_depth_241_);
v_res_247_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(v_depth_boxed_246_, v_keys_242_, v_vals_243_, v_i_244_, v_entries_245_);
lean_dec_ref(v_vals_243_);
lean_dec_ref(v_keys_242_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_x_248_, lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
size_t v_x_8118__boxed_253_; size_t v_x_8119__boxed_254_; lean_object* v_res_255_; 
v_x_8118__boxed_253_ = lean_unbox_usize(v_x_249_);
lean_dec(v_x_249_);
v_x_8119__boxed_254_ = lean_unbox_usize(v_x_250_);
lean_dec(v_x_250_);
v_res_255_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_x_248_, v_x_8118__boxed_253_, v_x_8119__boxed_254_, v_x_251_, v_x_252_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2___redArg(lean_object* v_x_256_, lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
uint64_t v___x_259_; size_t v___x_260_; size_t v___x_261_; lean_object* v___x_262_; 
v___x_259_ = l_Lean_instHashableLevelMVarId_hash(v_x_257_);
v___x_260_ = lean_uint64_to_usize(v___x_259_);
v___x_261_ = ((size_t)1ULL);
v___x_262_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_x_256_, v___x_260_, v___x_261_, v_x_257_, v_x_258_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(lean_object* v_mvarId_263_, lean_object* v_val_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___x_267_; lean_object* v_mctx_268_; lean_object* v_cache_269_; lean_object* v_zetaDeltaFVarIds_270_; lean_object* v_postponed_271_; lean_object* v_diag_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_301_; 
v___x_267_ = lean_st_ref_take(v___y_265_);
v_mctx_268_ = lean_ctor_get(v___x_267_, 0);
v_cache_269_ = lean_ctor_get(v___x_267_, 1);
v_zetaDeltaFVarIds_270_ = lean_ctor_get(v___x_267_, 2);
v_postponed_271_ = lean_ctor_get(v___x_267_, 3);
v_diag_272_ = lean_ctor_get(v___x_267_, 4);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_301_ == 0)
{
v___x_274_ = v___x_267_;
v_isShared_275_ = v_isSharedCheck_301_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_diag_272_);
lean_inc(v_postponed_271_);
lean_inc(v_zetaDeltaFVarIds_270_);
lean_inc(v_cache_269_);
lean_inc(v_mctx_268_);
lean_dec(v___x_267_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_301_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v_depth_276_; lean_object* v_levelAssignDepth_277_; lean_object* v_lmvarCounter_278_; lean_object* v_mvarCounter_279_; lean_object* v_lDecls_280_; lean_object* v_decls_281_; lean_object* v_userNames_282_; lean_object* v_lAssignment_283_; lean_object* v_eAssignment_284_; lean_object* v_dAssignment_285_; lean_object* v_instanceTypedMVars_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_300_; 
v_depth_276_ = lean_ctor_get(v_mctx_268_, 0);
v_levelAssignDepth_277_ = lean_ctor_get(v_mctx_268_, 1);
v_lmvarCounter_278_ = lean_ctor_get(v_mctx_268_, 2);
v_mvarCounter_279_ = lean_ctor_get(v_mctx_268_, 3);
v_lDecls_280_ = lean_ctor_get(v_mctx_268_, 4);
v_decls_281_ = lean_ctor_get(v_mctx_268_, 5);
v_userNames_282_ = lean_ctor_get(v_mctx_268_, 6);
v_lAssignment_283_ = lean_ctor_get(v_mctx_268_, 7);
v_eAssignment_284_ = lean_ctor_get(v_mctx_268_, 8);
v_dAssignment_285_ = lean_ctor_get(v_mctx_268_, 9);
v_instanceTypedMVars_286_ = lean_ctor_get(v_mctx_268_, 10);
v_isSharedCheck_300_ = !lean_is_exclusive(v_mctx_268_);
if (v_isSharedCheck_300_ == 0)
{
v___x_288_ = v_mctx_268_;
v_isShared_289_ = v_isSharedCheck_300_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_instanceTypedMVars_286_);
lean_inc(v_dAssignment_285_);
lean_inc(v_eAssignment_284_);
lean_inc(v_lAssignment_283_);
lean_inc(v_userNames_282_);
lean_inc(v_decls_281_);
lean_inc(v_lDecls_280_);
lean_inc(v_mvarCounter_279_);
lean_inc(v_lmvarCounter_278_);
lean_inc(v_levelAssignDepth_277_);
lean_inc(v_depth_276_);
lean_dec(v_mctx_268_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_300_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_290_ = lean_box(0);
v___x_291_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2___redArg(v_lAssignment_283_, v_mvarId_263_, v_val_264_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 7, v___x_291_);
v___x_293_ = v___x_288_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_depth_276_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_levelAssignDepth_277_);
lean_ctor_set(v_reuseFailAlloc_299_, 2, v_lmvarCounter_278_);
lean_ctor_set(v_reuseFailAlloc_299_, 3, v_mvarCounter_279_);
lean_ctor_set(v_reuseFailAlloc_299_, 4, v_lDecls_280_);
lean_ctor_set(v_reuseFailAlloc_299_, 5, v_decls_281_);
lean_ctor_set(v_reuseFailAlloc_299_, 6, v_userNames_282_);
lean_ctor_set(v_reuseFailAlloc_299_, 7, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_299_, 8, v_eAssignment_284_);
lean_ctor_set(v_reuseFailAlloc_299_, 9, v_dAssignment_285_);
lean_ctor_set(v_reuseFailAlloc_299_, 10, v_instanceTypedMVars_286_);
v___x_293_ = v_reuseFailAlloc_299_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_295_; 
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 0, v___x_293_);
v___x_295_ = v___x_274_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_cache_269_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v_zetaDeltaFVarIds_270_);
lean_ctor_set(v_reuseFailAlloc_298_, 3, v_postponed_271_);
lean_ctor_set(v_reuseFailAlloc_298_, 4, v_diag_272_);
v___x_295_ = v_reuseFailAlloc_298_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_st_ref_put(v___y_265_, v___x_295_);
v___x_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_290_);
return v___x_297_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_302_, lean_object* v_val_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(v_mvarId_302_, v_val_303_, v___y_304_);
lean_dec(v___y_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_307_, lean_object* v_vals_308_, lean_object* v_i_309_, lean_object* v_k_310_){
_start:
{
lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_311_ = lean_array_get_size(v_keys_307_);
v___x_312_ = lean_nat_dec_lt(v_i_309_, v___x_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; 
lean_dec(v_i_309_);
v___x_313_ = lean_box(0);
return v___x_313_;
}
else
{
lean_object* v_k_x27_314_; uint8_t v___x_315_; 
v_k_x27_314_ = lean_array_fget_borrowed(v_keys_307_, v_i_309_);
v___x_315_ = l_Lean_instBEqLevelMVarId_beq(v_k_310_, v_k_x27_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_unsigned_to_nat(1u);
v___x_317_ = lean_nat_add(v_i_309_, v___x_316_);
lean_dec(v_i_309_);
v_i_309_ = v___x_317_;
goto _start;
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_array_fget_borrowed(v_vals_308_, v_i_309_);
lean_dec(v_i_309_);
lean_inc(v___x_319_);
v___x_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_321_, lean_object* v_vals_322_, lean_object* v_i_323_, lean_object* v_k_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg(v_keys_321_, v_vals_322_, v_i_323_, v_k_324_);
lean_dec(v_k_324_);
lean_dec_ref(v_vals_322_);
lean_dec_ref(v_keys_321_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(lean_object* v_x_326_, size_t v_x_327_, lean_object* v_x_328_){
_start:
{
if (lean_obj_tag(v_x_326_) == 0)
{
lean_object* v_es_329_; lean_object* v___x_330_; size_t v___x_331_; size_t v___x_332_; lean_object* v_j_333_; lean_object* v___x_334_; 
v_es_329_ = lean_ctor_get(v_x_326_, 0);
v___x_330_ = lean_box(2);
v___x_331_ = ((size_t)31ULL);
v___x_332_ = lean_usize_land(v_x_327_, v___x_331_);
v_j_333_ = lean_usize_to_nat(v___x_332_);
v___x_334_ = lean_array_get_borrowed(v___x_330_, v_es_329_, v_j_333_);
lean_dec(v_j_333_);
switch(lean_obj_tag(v___x_334_))
{
case 0:
{
lean_object* v_key_335_; lean_object* v_val_336_; uint8_t v___x_337_; 
v_key_335_ = lean_ctor_get(v___x_334_, 0);
v_val_336_ = lean_ctor_get(v___x_334_, 1);
v___x_337_ = l_Lean_instBEqLevelMVarId_beq(v_x_328_, v_key_335_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; 
v___x_338_ = lean_box(0);
return v___x_338_;
}
else
{
lean_object* v___x_339_; 
lean_inc(v_val_336_);
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v_val_336_);
return v___x_339_;
}
}
case 1:
{
lean_object* v_node_340_; size_t v___x_341_; size_t v___x_342_; 
v_node_340_ = lean_ctor_get(v___x_334_, 0);
v___x_341_ = ((size_t)5ULL);
v___x_342_ = lean_usize_shift_right(v_x_327_, v___x_341_);
v_x_326_ = v_node_340_;
v_x_327_ = v___x_342_;
goto _start;
}
default: 
{
lean_object* v___x_344_; 
v___x_344_ = lean_box(0);
return v___x_344_;
}
}
}
else
{
lean_object* v_ks_345_; lean_object* v_vs_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_ks_345_ = lean_ctor_get(v_x_326_, 0);
v_vs_346_ = lean_ctor_get(v_x_326_, 1);
v___x_347_ = lean_unsigned_to_nat(0u);
v___x_348_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg(v_ks_345_, v_vs_346_, v___x_347_, v_x_328_);
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_349_, lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
size_t v_x_8346__boxed_352_; lean_object* v_res_353_; 
v_x_8346__boxed_352_ = lean_unbox_usize(v_x_350_);
lean_dec(v_x_350_);
v_res_353_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(v_x_349_, v_x_8346__boxed_352_, v_x_351_);
lean_dec(v_x_351_);
lean_dec_ref(v_x_349_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg(lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
uint64_t v___x_356_; size_t v___x_357_; lean_object* v___x_358_; 
v___x_356_ = l_Lean_instHashableLevelMVarId_hash(v_x_355_);
v___x_357_ = lean_uint64_to_usize(v___x_356_);
v___x_358_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(v_x_354_, v___x_357_, v_x_355_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg___boxed(lean_object* v_x_359_, lean_object* v_x_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg(v_x_359_, v_x_360_);
lean_dec(v_x_360_);
lean_dec_ref(v_x_359_);
return v_res_361_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3));
v___x_373_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__5));
v___x_374_ = l_Lean_Name_append(v___x_373_, v___x_372_);
return v___x_374_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__7));
v___x_377_ = l_Lean_stringToMessageData(v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__9));
v___x_380_ = l_Lean_stringToMessageData(v___x_379_);
return v___x_380_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_384_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__13));
v___x_385_ = lean_unsigned_to_nat(24u);
v___x_386_ = lean_unsigned_to_nat(55u);
v___x_387_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__12));
v___x_388_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__11));
v___x_389_ = l_mkPanicMessageWithDecl(v___x_388_, v___x_387_, v___x_386_, v___x_385_, v___x_384_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(lean_object* v_x_390_, uint8_t v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_u_401_; lean_object* v_v_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; 
switch(lean_obj_tag(v_x_390_))
{
case 0:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_box(0);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
case 4:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
lean_dec_ref_known(v_x_390_, 1);
v___x_431_ = lean_box(0);
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
case 5:
{
lean_object* v_a_433_; lean_object* v___x_434_; lean_object* v_mctx_435_; lean_object* v_lAssignment_436_; lean_object* v___x_437_; 
v_a_433_ = lean_ctor_get(v_x_390_, 0);
lean_inc(v_a_433_);
lean_dec_ref_known(v_x_390_, 1);
v___x_434_ = lean_st_ref_get(v_a_393_);
v_mctx_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc_ref(v_mctx_435_);
lean_dec(v___x_434_);
v_lAssignment_436_ = lean_ctor_get(v_mctx_435_, 7);
lean_inc_ref(v_lAssignment_436_);
lean_dec_ref(v_mctx_435_);
v___x_437_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg(v_lAssignment_436_, v_a_433_);
lean_dec_ref(v_lAssignment_436_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v___x_438_; 
lean_inc(v_a_433_);
v___x_438_ = l_Lean_LMVarId_isReadOnly(v_a_433_, v_a_392_, v_a_393_, v_a_394_, v_a_395_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_510_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_510_ == 0)
{
v___x_441_ = v___x_438_;
v_isShared_442_ = v_isSharedCheck_510_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_510_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
uint8_t v___x_443_; 
v___x_443_ = lean_unbox(v_a_439_);
lean_dec(v_a_439_);
if (v___x_443_ == 0)
{
if (v_a_391_ == 0)
{
lean_object* v___x_445_; 
lean_dec(v_a_433_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_437_);
v___x_445_ = v___x_441_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_437_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
else
{
lean_object* v___x_447_; 
lean_del_object(v___x_441_);
v___x_447_ = l_Lean_Meta_mkFreshLevelMVar(v_a_392_, v_a_393_, v_a_394_, v_a_395_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; uint8_t v___y_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v_toCold_474_; lean_object* v_options_475_; uint8_t v_hasTrace_476_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v___x_447_, 1);
v_toCold_474_ = lean_ctor_get(v_a_394_, 0);
v_options_475_ = lean_ctor_get(v_toCold_474_, 2);
v_hasTrace_476_ = lean_ctor_get_uint8(v_options_475_, sizeof(void*)*1);
if (v_hasTrace_476_ == 0)
{
v___y_450_ = v_a_391_;
v___y_451_ = v_a_392_;
v___y_452_ = v_a_393_;
v___y_453_ = v_a_394_;
v___y_454_ = v_a_395_;
goto v___jp_449_;
}
else
{
lean_object* v_inheritedTraceOptions_477_; lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v_inheritedTraceOptions_477_ = lean_ctor_get(v_toCold_474_, 11);
v___x_478_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3));
v___x_479_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6_once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6);
v___x_480_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_477_, v_options_475_, v___x_479_);
if (v___x_480_ == 0)
{
v___y_450_ = v_a_391_;
v___y_451_ = v_a_392_;
v___y_452_ = v_a_393_;
v___y_453_ = v_a_394_;
v___y_454_ = v_a_395_;
goto v___jp_449_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_481_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8_once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8);
lean_inc(v_a_433_);
v___x_482_ = l_Lean_mkLevelMVar(v_a_433_);
v___x_483_ = l_Lean_MessageData_ofLevel(v___x_482_);
v___x_484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_481_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10_once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10);
v___x_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
lean_inc(v_a_448_);
v___x_487_ = l_Lean_Level_succ___override(v_a_448_);
v___x_488_ = l_Lean_MessageData_ofLevel(v___x_487_);
v___x_489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_486_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg(v___x_478_, v___x_489_, v_a_392_, v_a_393_, v_a_394_, v_a_395_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_dec_ref_known(v___x_490_, 1);
v___y_450_ = v_a_391_;
v___y_451_ = v_a_392_;
v___y_452_ = v_a_393_;
v___y_453_ = v_a_394_;
v___y_454_ = v_a_395_;
goto v___jp_449_;
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec(v_a_448_);
lean_dec(v_a_433_);
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
v___jp_449_:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
lean_inc(v_a_448_);
v___x_455_ = l_Lean_Level_succ___override(v_a_448_);
v___x_456_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(v_a_433_, v___x_455_, v___y_452_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_464_; 
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; 
v_unused_465_ = lean_ctor_get(v___x_456_, 0);
lean_dec(v_unused_465_);
v___x_458_ = v___x_456_;
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
else
{
lean_dec(v___x_456_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_460_, 0, v_a_448_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_460_);
v___x_462_ = v___x_458_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_dec(v_a_448_);
v_a_466_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_456_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_456_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_dec(v_a_433_);
v_a_499_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_447_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_447_);
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
else
{
lean_object* v___x_508_; 
lean_dec(v_a_433_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_437_);
v___x_508_ = v___x_441_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_437_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
lean_dec(v_a_433_);
v_a_511_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_438_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_438_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
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
lean_object* v_val_519_; 
lean_dec(v_a_433_);
v_val_519_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_val_519_);
lean_dec_ref_known(v___x_437_, 1);
v_x_390_ = v_val_519_;
goto _start;
}
}
case 1:
{
lean_object* v_a_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v_a_521_ = lean_ctor_get(v_x_390_, 0);
lean_inc(v_a_521_);
lean_dec_ref_known(v_x_390_, 1);
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v_a_521_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
default: 
{
switch(lean_obj_tag(v_x_390_))
{
case 2:
{
lean_object* v_a_524_; lean_object* v_a_525_; 
v_a_524_ = lean_ctor_get(v_x_390_, 0);
lean_inc(v_a_524_);
v_a_525_ = lean_ctor_get(v_x_390_, 1);
lean_inc(v_a_525_);
lean_dec_ref_known(v_x_390_, 2);
v_u_401_ = v_a_524_;
v_v_402_ = v_a_525_;
v___y_403_ = v_a_392_;
v___y_404_ = v_a_393_;
v___y_405_ = v_a_394_;
v___y_406_ = v_a_395_;
goto v___jp_400_;
}
case 3:
{
lean_object* v_a_526_; lean_object* v_a_527_; 
v_a_526_ = lean_ctor_get(v_x_390_, 0);
lean_inc(v_a_526_);
v_a_527_ = lean_ctor_get(v_x_390_, 1);
lean_inc(v_a_527_);
lean_dec_ref_known(v_x_390_, 2);
v_u_401_ = v_a_526_;
v_v_402_ = v_a_527_;
v___y_403_ = v_a_392_;
v___y_404_ = v_a_393_;
v___y_405_ = v_a_394_;
v___y_406_ = v_a_395_;
goto v___jp_400_;
}
default: 
{
lean_object* v___x_528_; lean_object* v___x_529_; 
lean_dec(v_x_390_);
v___x_528_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14_once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14);
v___x_529_ = l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3(v___x_528_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_);
return v___x_529_;
}
}
}
}
v___jp_397_:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_box(0);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
v___jp_400_:
{
uint8_t v___x_407_; lean_object* v___x_408_; 
v___x_407_ = 0;
v___x_408_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(v_u_401_, v___x_407_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_408_, 1);
if (lean_obj_tag(v_a_409_) == 0)
{
lean_dec(v_v_402_);
goto v___jp_397_;
}
else
{
lean_object* v_val_410_; lean_object* v___x_411_; 
v_val_410_ = lean_ctor_get(v_a_409_, 0);
lean_inc(v_val_410_);
lean_dec_ref_known(v_a_409_, 1);
v___x_411_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(v_v_402_, v___x_407_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_428_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_428_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_428_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_428_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
if (lean_obj_tag(v_a_412_) == 0)
{
lean_del_object(v___x_414_);
lean_dec(v_val_410_);
goto v___jp_397_;
}
else
{
lean_object* v_val_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_427_; 
v_val_416_ = lean_ctor_get(v_a_412_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v_a_412_);
if (v_isSharedCheck_427_ == 0)
{
v___x_418_ = v_a_412_;
v_isShared_419_ = v_isSharedCheck_427_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_val_416_);
lean_dec(v_a_412_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_427_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_420_ = l_Lean_mkLevelMax_x27(v_val_410_, v_val_416_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_420_);
v___x_422_ = v___x_418_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_420_);
v___x_422_ = v_reuseFailAlloc_426_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_424_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_422_);
v___x_424_ = v___x_414_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
}
else
{
lean_dec(v_val_410_);
return v___x_411_;
}
}
}
else
{
lean_dec(v_v_402_);
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___boxed(lean_object* v_x_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
uint8_t v_a_boxed_537_; lean_object* v_res_538_; 
v_a_boxed_537_ = lean_unbox(v_a_531_);
v_res_538_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(v_x_530_, v_a_boxed_537_, v_a_532_, v_a_533_, v_a_534_, v_a_535_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_532_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0(lean_object* v_00_u03b2_539_, lean_object* v_x_540_, lean_object* v_x_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg(v_x_540_, v_x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___boxed(lean_object* v_00_u03b2_543_, lean_object* v_x_544_, lean_object* v_x_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0(v_00_u03b2_543_, v_x_544_, v_x_545_);
lean_dec(v_x_545_);
lean_dec_ref(v_x_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1(lean_object* v_mvarId_547_, lean_object* v_val_548_, uint8_t v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(v_mvarId_547_, v_val_548_, v___y_551_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___boxed(lean_object* v_mvarId_556_, lean_object* v_val_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
uint8_t v___y_8757__boxed_564_; lean_object* v_res_565_; 
v___y_8757__boxed_564_ = lean_unbox(v___y_558_);
v_res_565_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1(v_mvarId_556_, v_val_557_, v___y_8757__boxed_564_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2(lean_object* v_cls_566_, lean_object* v_msg_567_, uint8_t v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg(v_cls_566_, v_msg_567_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___boxed(lean_object* v_cls_575_, lean_object* v_msg_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
uint8_t v___y_8777__boxed_583_; lean_object* v_res_584_; 
v___y_8777__boxed_583_ = lean_unbox(v___y_577_);
v_res_584_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2(v_cls_575_, v_msg_576_, v___y_8777__boxed_583_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0(lean_object* v_00_u03b2_585_, lean_object* v_x_586_, size_t v_x_587_, lean_object* v_x_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(v_x_586_, v_x_587_, v_x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_590_, lean_object* v_x_591_, lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
size_t v_x_8798__boxed_594_; lean_object* v_res_595_; 
v_x_8798__boxed_594_ = lean_unbox_usize(v_x_592_);
lean_dec(v_x_592_);
v_res_595_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0(v_00_u03b2_590_, v_x_591_, v_x_8798__boxed_594_, v_x_593_);
lean_dec(v_x_593_);
lean_dec_ref(v_x_591_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2(lean_object* v_00_u03b2_596_, lean_object* v_x_597_, lean_object* v_x_598_, lean_object* v_x_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2___redArg(v_x_597_, v_x_598_, v_x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_601_, lean_object* v_keys_602_, lean_object* v_vals_603_, lean_object* v_heq_604_, lean_object* v_i_605_, lean_object* v_k_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg(v_keys_602_, v_vals_603_, v_i_605_, v_k_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_608_, lean_object* v_keys_609_, lean_object* v_vals_610_, lean_object* v_heq_611_, lean_object* v_i_612_, lean_object* v_k_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2(v_00_u03b2_608_, v_keys_609_, v_vals_610_, v_heq_611_, v_i_612_, v_k_613_);
lean_dec(v_k_613_);
lean_dec_ref(v_vals_610_);
lean_dec_ref(v_keys_609_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_615_, lean_object* v_x_616_, size_t v_x_617_, size_t v_x_618_, lean_object* v_x_619_, lean_object* v_x_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_x_616_, v_x_617_, v_x_618_, v_x_619_, v_x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_622_, lean_object* v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_, lean_object* v_x_626_, lean_object* v_x_627_){
_start:
{
size_t v_x_8819__boxed_628_; size_t v_x_8820__boxed_629_; lean_object* v_res_630_; 
v_x_8819__boxed_628_ = lean_unbox_usize(v_x_624_);
lean_dec(v_x_624_);
v_x_8820__boxed_629_ = lean_unbox_usize(v_x_625_);
lean_dec(v_x_625_);
v_res_630_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5(v_00_u03b2_622_, v_x_623_, v_x_8819__boxed_628_, v_x_8820__boxed_629_, v_x_626_, v_x_627_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_631_, lean_object* v_n_632_, lean_object* v_k_633_, lean_object* v_v_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8___redArg(v_n_632_, v_k_633_, v_v_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_636_, size_t v_depth_637_, lean_object* v_keys_638_, lean_object* v_vals_639_, lean_object* v_heq_640_, lean_object* v_i_641_, lean_object* v_entries_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(v_depth_637_, v_keys_638_, v_vals_639_, v_i_641_, v_entries_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03b2_644_, lean_object* v_depth_645_, lean_object* v_keys_646_, lean_object* v_vals_647_, lean_object* v_heq_648_, lean_object* v_i_649_, lean_object* v_entries_650_){
_start:
{
size_t v_depth_boxed_651_; lean_object* v_res_652_; 
v_depth_boxed_651_ = lean_unbox_usize(v_depth_645_);
lean_dec(v_depth_645_);
v_res_652_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9(v_00_u03b2_644_, v_depth_boxed_651_, v_keys_646_, v_vals_647_, v_heq_648_, v_i_649_, v_entries_650_);
lean_dec_ref(v_vals_647_);
lean_dec_ref(v_keys_646_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8_spec__9(lean_object* v_00_u03b2_653_, lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v_x_656_, lean_object* v_x_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8_spec__9___redArg(v_x_654_, v_x_655_, v_x_656_, v_x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel_x3f(lean_object* v_u_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v___x_665_; lean_object* v_mctx_666_; uint8_t v___x_667_; lean_object* v___x_668_; 
v___x_665_ = lean_st_ref_get(v_a_661_);
v_mctx_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc_ref(v_mctx_666_);
lean_dec(v___x_665_);
v___x_667_ = 1;
v___x_668_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(v_u_659_, v___x_667_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
if (lean_obj_tag(v_a_669_) == 0)
{
lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_690_; 
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_690_ == 0)
{
lean_object* v_unused_691_; 
v_unused_691_ = lean_ctor_get(v___x_668_, 0);
lean_dec(v_unused_691_);
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_690_;
goto v_resetjp_670_;
}
else
{
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_690_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v_cache_674_; lean_object* v_zetaDeltaFVarIds_675_; lean_object* v_postponed_676_; lean_object* v_diag_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_688_; 
v___x_673_ = lean_st_ref_take(v_a_661_);
v_cache_674_ = lean_ctor_get(v___x_673_, 1);
v_zetaDeltaFVarIds_675_ = lean_ctor_get(v___x_673_, 2);
v_postponed_676_ = lean_ctor_get(v___x_673_, 3);
v_diag_677_ = lean_ctor_get(v___x_673_, 4);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; 
v_unused_689_ = lean_ctor_get(v___x_673_, 0);
lean_dec(v_unused_689_);
v___x_679_ = v___x_673_;
v_isShared_680_ = v_isSharedCheck_688_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_diag_677_);
lean_inc(v_postponed_676_);
lean_inc(v_zetaDeltaFVarIds_675_);
lean_inc(v_cache_674_);
lean_dec(v___x_673_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_688_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 0, v_mctx_666_);
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_mctx_666_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_cache_674_);
lean_ctor_set(v_reuseFailAlloc_687_, 2, v_zetaDeltaFVarIds_675_);
lean_ctor_set(v_reuseFailAlloc_687_, 3, v_postponed_676_);
lean_ctor_set(v_reuseFailAlloc_687_, 4, v_diag_677_);
v___x_682_ = v_reuseFailAlloc_687_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_683_ = lean_st_ref_put(v_a_661_, v___x_682_);
if (v_isShared_672_ == 0)
{
v___x_685_ = v___x_671_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_669_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_a_669_, 1);
lean_dec_ref(v_mctx_666_);
return v___x_668_;
}
}
else
{
lean_dec_ref(v_mctx_666_);
return v___x_668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel_x3f___boxed(lean_object* v_u_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_Meta_decLevel_x3f(v_u_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(lean_object* v_msg_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_ref_705_; lean_object* v___x_706_; lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_715_; 
v_ref_705_ = lean_ctor_get(v___y_702_, 2);
v___x_706_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4(v_msg_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
v_a_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_715_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_715_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_715_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_713_; 
lean_inc(v_ref_705_);
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v_ref_705_);
lean_ctor_set(v___x_711_, 1, v_a_707_);
if (v_isShared_710_ == 0)
{
lean_ctor_set_tag(v___x_709_, 1);
lean_ctor_set(v___x_709_, 0, v___x_711_);
v___x_713_ = v___x_709_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg___boxed(lean_object* v_msg_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(v_msg_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
return v_res_722_;
}
}
static lean_object* _init_l_Lean_Meta_decLevel___closed__1(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = ((lean_object*)(l_Lean_Meta_decLevel___closed__0));
v___x_725_ = l_Lean_stringToMessageData(v___x_724_);
return v___x_725_;
}
}
static lean_object* _init_l_Lean_Meta_decLevel___closed__3(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = ((lean_object*)(l_Lean_Meta_decLevel___closed__2));
v___x_728_ = l_Lean_stringToMessageData(v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel(lean_object* v_u_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_735_; 
lean_inc(v_u_729_);
v___x_735_ = l_Lean_Meta_decLevel_x3f(v_u_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_750_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_750_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_750_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_750_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
if (lean_obj_tag(v_a_736_) == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
lean_del_object(v___x_738_);
v___x_740_ = lean_obj_once(&l_Lean_Meta_decLevel___closed__1, &l_Lean_Meta_decLevel___closed__1_once, _init_l_Lean_Meta_decLevel___closed__1);
v___x_741_ = l_Lean_MessageData_ofLevel(v_u_729_);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = lean_obj_once(&l_Lean_Meta_decLevel___closed__3, &l_Lean_Meta_decLevel___closed__3_once, _init_l_Lean_Meta_decLevel___closed__3);
v___x_744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(v___x_744_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
return v___x_745_;
}
else
{
lean_object* v_val_746_; lean_object* v___x_748_; 
lean_dec(v_u_729_);
v_val_746_ = lean_ctor_get(v_a_736_, 0);
lean_inc(v_val_746_);
lean_dec_ref_known(v_a_736_, 1);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v_val_746_);
v___x_748_ = v___x_738_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_val_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec(v_u_729_);
v_a_751_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_735_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_735_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel___boxed(lean_object* v_u_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_Meta_decLevel(v_u_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0(lean_object* v_00_u03b1_766_, lean_object* v_msg_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(v_msg_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___boxed(lean_object* v_00_u03b1_774_, lean_object* v_msg_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0(v_00_u03b1_774_, v_msg_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel(lean_object* v_type_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_Meta_getLevel(v_type_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_790_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_788_, 1);
v___x_790_ = l_Lean_Meta_normalizeLevel(v_a_789_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v___x_792_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_791_);
lean_dec_ref_known(v___x_790_, 1);
v___x_792_ = l_Lean_Meta_decLevel(v_a_791_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
return v___x_792_;
}
else
{
return v___x_790_;
}
}
else
{
return v___x_788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel___boxed(lean_object* v_type_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_Meta_getDecLevel(v_type_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel_x3f(lean_object* v_type_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
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
v___x_810_ = l_Lean_Meta_decLevel_x3f(v_a_809_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
return v___x_810_;
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
v_a_811_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_808_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_808_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
v_a_819_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_806_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_806_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel_x3f___boxed(lean_object* v_type_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_Meta_getDecLevel_x3f(v_type_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
return v_res_833_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_875_ = lean_unsigned_to_nat(3263537904u);
v___x_876_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_));
v___x_877_ = l_Lean_Name_num___override(v___x_876_, v___x_875_);
return v___x_877_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_879_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_));
v___x_880_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_);
v___x_881_ = l_Lean_Name_str___override(v___x_880_, v___x_879_);
return v___x_881_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_883_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_));
v___x_884_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_);
v___x_885_ = l_Lean_Name_str___override(v___x_884_, v___x_883_);
return v___x_885_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_886_ = lean_unsigned_to_nat(2u);
v___x_887_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_);
v___x_888_ = l_Lean_Name_num___override(v___x_887_, v___x_886_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_890_; uint8_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_890_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3));
v___x_891_ = 0;
v___x_892_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_);
v___x_893_ = l_Lean_registerTraceClass(v___x_890_, v___x_891_, v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2____boxed(lean_object* v_a_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_();
return v_res_895_;
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
