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
uint64_t l_Lean_instHashableLevelMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
lean_object* v___f_9_; lean_object* v___f_10_; lean_object* v___x_7837__overap_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___f_9_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3___closed__0));
v___f_10_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_10_, 0, v___f_9_);
v___x_7837__overap_11_ = lean_panic_fn_borrowed(v___f_10_, v_msg_2_);
lean_dec_ref(v___f_10_);
v___x_12_ = lean_box(v___y_3_);
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_5_);
lean_inc_ref(v___y_4_);
v___x_13_ = lean_apply_6(v___x_7837__overap_11_, v___x_12_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3___boxed(lean_object* v_msg_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_){
_start:
{
uint8_t v___y_8696__boxed_21_; lean_object* v_res_22_; 
v___y_8696__boxed_21_ = lean_unbox(v___y_15_);
v_res_22_ = l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3(v_msg_14_, v___y_8696__boxed_21_, v___y_16_, v___y_17_, v___y_18_, v___y_19_);
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
lean_object* v_ks_199_; lean_object* v_vs_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_220_; 
v_ks_199_ = lean_ctor_get(v_x_148_, 0);
v_vs_200_ = lean_ctor_get(v_x_148_, 1);
v_isSharedCheck_220_ = !lean_is_exclusive(v_x_148_);
if (v_isSharedCheck_220_ == 0)
{
v___x_202_ = v_x_148_;
v_isShared_203_ = v_isSharedCheck_220_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_vs_200_);
lean_inc(v_ks_199_);
lean_dec(v_x_148_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_220_;
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
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_ks_199_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_vs_200_);
v___x_205_ = v_reuseFailAlloc_219_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v_newNode_206_; uint8_t v___y_208_; size_t v___x_214_; uint8_t v___x_215_; 
v_newNode_206_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8___redArg(v___x_205_, v_x_151_, v_x_152_);
v___x_214_ = ((size_t)7ULL);
v___x_215_ = lean_usize_dec_le(v___x_214_, v_x_150_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_216_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_206_);
v___x_217_ = lean_unsigned_to_nat(4u);
v___x_218_ = lean_nat_dec_lt(v___x_216_, v___x_217_);
lean_dec(v___x_216_);
v___y_208_ = v___x_218_;
goto v___jp_207_;
}
else
{
v___y_208_ = v___x_215_;
goto v___jp_207_;
}
v___jp_207_:
{
if (v___y_208_ == 0)
{
lean_object* v_ks_209_; lean_object* v_vs_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_ks_209_ = lean_ctor_get(v_newNode_206_, 0);
lean_inc_ref(v_ks_209_);
v_vs_210_ = lean_ctor_get(v_newNode_206_, 1);
lean_inc_ref(v_vs_210_);
lean_dec_ref(v_newNode_206_);
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_213_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(v_x_150_, v_ks_209_, v_vs_210_, v___x_211_, v___x_212_);
lean_dec_ref(v_vs_210_);
lean_dec_ref(v_ks_209_);
return v___x_213_;
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
size_t v_x_8926__boxed_253_; size_t v_x_8927__boxed_254_; lean_object* v_res_255_; 
v_x_8926__boxed_253_ = lean_unbox_usize(v_x_249_);
lean_dec(v_x_249_);
v_x_8927__boxed_254_ = lean_unbox_usize(v_x_250_);
lean_dec(v_x_250_);
v_res_255_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_x_248_, v_x_8926__boxed_253_, v_x_8927__boxed_254_, v_x_251_, v_x_252_);
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
lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_290_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2___redArg(v_lAssignment_283_, v_mvarId_263_, v_val_264_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 7, v___x_290_);
v___x_292_ = v___x_288_;
goto v_reusejp_291_;
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
lean_ctor_set(v_reuseFailAlloc_299_, 7, v___x_290_);
lean_ctor_set(v_reuseFailAlloc_299_, 8, v_eAssignment_284_);
lean_ctor_set(v_reuseFailAlloc_299_, 9, v_dAssignment_285_);
lean_ctor_set(v_reuseFailAlloc_299_, 10, v_instanceTypedMVars_286_);
v___x_292_ = v_reuseFailAlloc_299_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_294_; 
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 0, v___x_292_);
v___x_294_ = v___x_274_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_cache_269_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v_zetaDeltaFVarIds_270_);
lean_ctor_set(v_reuseFailAlloc_298_, 3, v_postponed_271_);
lean_ctor_set(v_reuseFailAlloc_298_, 4, v_diag_272_);
v___x_294_ = v_reuseFailAlloc_298_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = lean_st_ref_put(v___y_265_, v___x_294_);
v___x_296_ = lean_box(0);
v___x_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
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
size_t v_x_9158__boxed_352_; lean_object* v_res_353_; 
v_x_9158__boxed_352_ = lean_unbox_usize(v_x_350_);
lean_dec(v_x_350_);
v_res_353_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(v_x_349_, v_x_9158__boxed_352_, v_x_351_);
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
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_509_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_509_ == 0)
{
v___x_441_ = v___x_438_;
v_isShared_442_ = v_isSharedCheck_509_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_509_;
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
lean_object* v_a_448_; uint8_t v___y_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v_options_474_; uint8_t v_hasTrace_475_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v___x_447_, 1);
v_options_474_ = lean_ctor_get(v_a_394_, 2);
v_hasTrace_475_ = lean_ctor_get_uint8(v_options_474_, sizeof(void*)*1);
if (v_hasTrace_475_ == 0)
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
lean_object* v_inheritedTraceOptions_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v_inheritedTraceOptions_476_ = lean_ctor_get(v_a_394_, 13);
v___x_477_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3));
v___x_478_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6_once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__6);
v___x_479_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_476_, v_options_474_, v___x_478_);
if (v___x_479_ == 0)
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
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_480_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8_once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__8);
lean_inc(v_a_433_);
v___x_481_ = l_Lean_mkLevelMVar(v_a_433_);
v___x_482_ = l_Lean_MessageData_ofLevel(v___x_481_);
v___x_483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_480_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
v___x_484_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10_once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__10);
v___x_485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_483_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
lean_inc(v_a_448_);
v___x_486_ = l_Lean_Level_succ___override(v_a_448_);
v___x_487_ = l_Lean_MessageData_ofLevel(v___x_486_);
v___x_488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_485_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg(v___x_477_, v___x_488_, v_a_392_, v_a_393_, v_a_394_, v_a_395_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_dec_ref_known(v___x_489_, 1);
v___y_450_ = v_a_391_;
v___y_451_ = v_a_392_;
v___y_452_ = v_a_393_;
v___y_453_ = v_a_394_;
v___y_454_ = v_a_395_;
goto v___jp_449_;
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec(v_a_448_);
lean_dec(v_a_433_);
v_a_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
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
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec(v_a_433_);
v_a_498_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_447_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_447_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
else
{
lean_object* v___x_507_; 
lean_dec(v_a_433_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_437_);
v___x_507_ = v___x_441_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_437_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec(v_a_433_);
v_a_510_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_438_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_438_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
else
{
lean_object* v_val_518_; 
lean_dec(v_a_433_);
v_val_518_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_val_518_);
lean_dec_ref_known(v___x_437_, 1);
v_x_390_ = v_val_518_;
goto _start;
}
}
case 1:
{
lean_object* v_a_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_a_520_ = lean_ctor_get(v_x_390_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v_x_390_, 1);
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v_a_520_);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
default: 
{
switch(lean_obj_tag(v_x_390_))
{
case 2:
{
lean_object* v_a_523_; lean_object* v_a_524_; 
v_a_523_ = lean_ctor_get(v_x_390_, 0);
lean_inc(v_a_523_);
v_a_524_ = lean_ctor_get(v_x_390_, 1);
lean_inc(v_a_524_);
lean_dec_ref_known(v_x_390_, 2);
v_u_401_ = v_a_523_;
v_v_402_ = v_a_524_;
v___y_403_ = v_a_392_;
v___y_404_ = v_a_393_;
v___y_405_ = v_a_394_;
v___y_406_ = v_a_395_;
goto v___jp_400_;
}
case 3:
{
lean_object* v_a_525_; lean_object* v_a_526_; 
v_a_525_ = lean_ctor_get(v_x_390_, 0);
lean_inc(v_a_525_);
v_a_526_ = lean_ctor_get(v_x_390_, 1);
lean_inc(v_a_526_);
lean_dec_ref_known(v_x_390_, 2);
v_u_401_ = v_a_525_;
v_v_402_ = v_a_526_;
v___y_403_ = v_a_392_;
v___y_404_ = v_a_393_;
v___y_405_ = v_a_394_;
v___y_406_ = v_a_395_;
goto v___jp_400_;
}
default: 
{
lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec(v_x_390_);
v___x_527_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14_once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__14);
v___x_528_ = l_panic___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__3(v___x_527_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_);
return v___x_528_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___boxed(lean_object* v_x_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
uint8_t v_a_boxed_536_; lean_object* v_res_537_; 
v_a_boxed_536_ = lean_unbox(v_a_530_);
v_res_537_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(v_x_529_, v_a_boxed_536_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0(lean_object* v_00_u03b2_538_, lean_object* v_x_539_, lean_object* v_x_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___redArg(v_x_539_, v_x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0___boxed(lean_object* v_00_u03b2_542_, lean_object* v_x_543_, lean_object* v_x_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0(v_00_u03b2_542_, v_x_543_, v_x_544_);
lean_dec(v_x_544_);
lean_dec_ref(v_x_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1(lean_object* v_mvarId_546_, lean_object* v_val_547_, uint8_t v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___redArg(v_mvarId_546_, v_val_547_, v___y_550_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1___boxed(lean_object* v_mvarId_555_, lean_object* v_val_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
uint8_t v___y_9569__boxed_563_; lean_object* v_res_564_; 
v___y_9569__boxed_563_ = lean_unbox(v___y_557_);
v_res_564_ = l_Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1(v_mvarId_555_, v_val_556_, v___y_9569__boxed_563_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2(lean_object* v_cls_565_, lean_object* v_msg_566_, uint8_t v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___redArg(v_cls_565_, v_msg_566_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2___boxed(lean_object* v_cls_574_, lean_object* v_msg_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
uint8_t v___y_9589__boxed_582_; lean_object* v_res_583_; 
v___y_9589__boxed_582_ = lean_unbox(v___y_576_);
v_res_583_ = l_Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2(v_cls_574_, v_msg_575_, v___y_9589__boxed_582_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0(lean_object* v_00_u03b2_584_, lean_object* v_x_585_, size_t v_x_586_, lean_object* v_x_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___redArg(v_x_585_, v_x_586_, v_x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_589_, lean_object* v_x_590_, lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
size_t v_x_9610__boxed_593_; lean_object* v_res_594_; 
v_x_9610__boxed_593_ = lean_unbox_usize(v_x_591_);
lean_dec(v_x_591_);
v_res_594_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0(v_00_u03b2_589_, v_x_590_, v_x_9610__boxed_593_, v_x_592_);
lean_dec(v_x_592_);
lean_dec_ref(v_x_590_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2(lean_object* v_00_u03b2_595_, lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_x_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2___redArg(v_x_596_, v_x_597_, v_x_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_600_, lean_object* v_keys_601_, lean_object* v_vals_602_, lean_object* v_heq_603_, lean_object* v_i_604_, lean_object* v_k_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___redArg(v_keys_601_, v_vals_602_, v_i_604_, v_k_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_607_, lean_object* v_keys_608_, lean_object* v_vals_609_, lean_object* v_heq_610_, lean_object* v_i_611_, lean_object* v_k_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__0_spec__0_spec__2(v_00_u03b2_607_, v_keys_608_, v_vals_609_, v_heq_610_, v_i_611_, v_k_612_);
lean_dec(v_k_612_);
lean_dec_ref(v_vals_609_);
lean_dec_ref(v_keys_608_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_614_, lean_object* v_x_615_, size_t v_x_616_, size_t v_x_617_, lean_object* v_x_618_, lean_object* v_x_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___redArg(v_x_615_, v_x_616_, v_x_617_, v_x_618_, v_x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_621_, lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
size_t v_x_9631__boxed_627_; size_t v_x_9632__boxed_628_; lean_object* v_res_629_; 
v_x_9631__boxed_627_ = lean_unbox_usize(v_x_623_);
lean_dec(v_x_623_);
v_x_9632__boxed_628_ = lean_unbox_usize(v_x_624_);
lean_dec(v_x_624_);
v_res_629_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5(v_00_u03b2_621_, v_x_622_, v_x_9631__boxed_627_, v_x_9632__boxed_628_, v_x_625_, v_x_626_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_630_, lean_object* v_n_631_, lean_object* v_k_632_, lean_object* v_v_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8___redArg(v_n_631_, v_k_632_, v_v_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_635_, size_t v_depth_636_, lean_object* v_keys_637_, lean_object* v_vals_638_, lean_object* v_heq_639_, lean_object* v_i_640_, lean_object* v_entries_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___redArg(v_depth_636_, v_keys_637_, v_vals_638_, v_i_640_, v_entries_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03b2_643_, lean_object* v_depth_644_, lean_object* v_keys_645_, lean_object* v_vals_646_, lean_object* v_heq_647_, lean_object* v_i_648_, lean_object* v_entries_649_){
_start:
{
size_t v_depth_boxed_650_; lean_object* v_res_651_; 
v_depth_boxed_650_ = lean_unbox_usize(v_depth_644_);
lean_dec(v_depth_644_);
v_res_651_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__9(v_00_u03b2_643_, v_depth_boxed_650_, v_keys_645_, v_vals_646_, v_heq_647_, v_i_648_, v_entries_649_);
lean_dec_ref(v_vals_646_);
lean_dec_ref(v_keys_645_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8_spec__9(lean_object* v_00_u03b2_652_, lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_assignLevelMVar___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__1_spec__2_spec__5_spec__8_spec__9___redArg(v_x_653_, v_x_654_, v_x_655_, v_x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel_x3f(lean_object* v_u_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v___x_664_; uint8_t v___x_665_; lean_object* v___x_666_; 
v___x_664_ = lean_st_ref_get(v_a_660_);
v___x_665_ = 1;
v___x_666_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f(v_u_658_, v___x_665_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
if (lean_obj_tag(v_a_667_) == 0)
{
lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_689_; 
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; 
v_unused_690_ = lean_ctor_get(v___x_666_, 0);
lean_dec(v_unused_690_);
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_689_;
goto v_resetjp_668_;
}
else
{
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_689_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v_mctx_672_; lean_object* v_cache_673_; lean_object* v_zetaDeltaFVarIds_674_; lean_object* v_postponed_675_; lean_object* v_diag_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_687_; 
v___x_671_ = lean_st_ref_take(v_a_660_);
v_mctx_672_ = lean_ctor_get(v___x_664_, 0);
lean_inc_ref(v_mctx_672_);
lean_dec(v___x_664_);
v_cache_673_ = lean_ctor_get(v___x_671_, 1);
v_zetaDeltaFVarIds_674_ = lean_ctor_get(v___x_671_, 2);
v_postponed_675_ = lean_ctor_get(v___x_671_, 3);
v_diag_676_ = lean_ctor_get(v___x_671_, 4);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_687_ == 0)
{
lean_object* v_unused_688_; 
v_unused_688_ = lean_ctor_get(v___x_671_, 0);
lean_dec(v_unused_688_);
v___x_678_ = v___x_671_;
v_isShared_679_ = v_isSharedCheck_687_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_diag_676_);
lean_inc(v_postponed_675_);
lean_inc(v_zetaDeltaFVarIds_674_);
lean_inc(v_cache_673_);
lean_dec(v___x_671_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_687_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v_mctx_672_);
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_mctx_672_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_cache_673_);
lean_ctor_set(v_reuseFailAlloc_686_, 2, v_zetaDeltaFVarIds_674_);
lean_ctor_set(v_reuseFailAlloc_686_, 3, v_postponed_675_);
lean_ctor_set(v_reuseFailAlloc_686_, 4, v_diag_676_);
v___x_681_ = v_reuseFailAlloc_686_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_682_ = lean_st_ref_put(v_a_660_, v___x_681_);
if (v_isShared_670_ == 0)
{
v___x_684_ = v___x_669_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_667_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_a_667_, 1);
lean_dec(v___x_664_);
return v___x_666_;
}
}
else
{
lean_dec(v___x_664_);
return v___x_666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel_x3f___boxed(lean_object* v_u_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_Meta_decLevel_x3f(v_u_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(lean_object* v_msg_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_ref_704_; lean_object* v___x_705_; lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_714_; 
v_ref_704_ = lean_ctor_get(v___y_701_, 5);
v___x_705_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f_spec__2_spec__4(v_msg_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
v_a_706_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_714_ == 0)
{
v___x_708_ = v___x_705_;
v_isShared_709_ = v_isSharedCheck_714_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_714_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
lean_inc(v_ref_704_);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v_ref_704_);
lean_ctor_set(v___x_710_, 1, v_a_706_);
if (v_isShared_709_ == 0)
{
lean_ctor_set_tag(v___x_708_, 1);
lean_ctor_set(v___x_708_, 0, v___x_710_);
v___x_712_ = v___x_708_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg___boxed(lean_object* v_msg_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(v_msg_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
return v_res_721_;
}
}
static lean_object* _init_l_Lean_Meta_decLevel___closed__1(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = ((lean_object*)(l_Lean_Meta_decLevel___closed__0));
v___x_724_ = l_Lean_stringToMessageData(v___x_723_);
return v___x_724_;
}
}
static lean_object* _init_l_Lean_Meta_decLevel___closed__3(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = ((lean_object*)(l_Lean_Meta_decLevel___closed__2));
v___x_727_ = l_Lean_stringToMessageData(v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel(lean_object* v_u_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
lean_object* v___x_734_; 
lean_inc(v_u_728_);
v___x_734_ = l_Lean_Meta_decLevel_x3f(v_u_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_749_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_749_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_749_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_749_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
if (lean_obj_tag(v_a_735_) == 0)
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
lean_del_object(v___x_737_);
v___x_739_ = lean_obj_once(&l_Lean_Meta_decLevel___closed__1, &l_Lean_Meta_decLevel___closed__1_once, _init_l_Lean_Meta_decLevel___closed__1);
v___x_740_ = l_Lean_MessageData_ofLevel(v_u_728_);
v___x_741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_739_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = lean_obj_once(&l_Lean_Meta_decLevel___closed__3, &l_Lean_Meta_decLevel___closed__3_once, _init_l_Lean_Meta_decLevel___closed__3);
v___x_743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(v___x_743_, v_a_729_, v_a_730_, v_a_731_, v_a_732_);
return v___x_744_;
}
else
{
lean_object* v_val_745_; lean_object* v___x_747_; 
lean_dec(v_u_728_);
v_val_745_ = lean_ctor_get(v_a_735_, 0);
lean_inc(v_val_745_);
lean_dec_ref_known(v_a_735_, 1);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v_val_745_);
v___x_747_ = v___x_737_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_val_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec(v_u_728_);
v_a_750_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_734_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_734_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_decLevel___boxed(lean_object* v_u_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_Meta_decLevel(v_u_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0(lean_object* v_00_u03b1_765_, lean_object* v_msg_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___redArg(v_msg_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0___boxed(lean_object* v_00_u03b1_773_, lean_object* v_msg_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_throwError___at___00Lean_Meta_decLevel_spec__0(v_00_u03b1_773_, v_msg_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel(lean_object* v_type_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_Meta_getLevel(v_type_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_789_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref_known(v___x_787_, 1);
v___x_789_ = l_Lean_Meta_normalizeLevel(v_a_788_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_791_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
lean_dec_ref_known(v___x_789_, 1);
v___x_791_ = l_Lean_Meta_decLevel(v_a_790_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
return v___x_791_;
}
else
{
return v___x_789_;
}
}
else
{
return v___x_787_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel___boxed(lean_object* v_type_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_Meta_getDecLevel(v_type_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
lean_dec(v_a_794_);
lean_dec_ref(v_a_793_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel_x3f(lean_object* v_type_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_Meta_getLevel(v_type_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_807_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref_known(v___x_805_, 1);
v___x_807_ = l_Lean_Meta_normalizeLevel(v_a_806_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_809_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref_known(v___x_807_, 1);
v___x_809_ = l_Lean_Meta_decLevel_x3f(v_a_808_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
return v___x_809_;
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
v_a_810_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_807_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_807_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
v_a_818_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_805_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_805_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDecLevel_x3f___boxed(lean_object* v_type_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_Meta_getDecLevel_x3f(v_type_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
return v_res_832_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_874_ = lean_unsigned_to_nat(3263537904u);
v___x_875_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_));
v___x_876_ = l_Lean_Name_num___override(v___x_875_, v___x_874_);
return v___x_876_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_878_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_));
v___x_879_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_);
v___x_880_ = l_Lean_Name_str___override(v___x_879_, v___x_878_);
return v___x_880_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_882_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_));
v___x_883_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_);
v___x_884_ = l_Lean_Name_str___override(v___x_883_, v___x_882_);
return v___x_884_;
}
}
static lean_object* _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_885_ = lean_unsigned_to_nat(2u);
v___x_886_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_);
v___x_887_ = l_Lean_Name_num___override(v___x_886_, v___x_885_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_889_; uint8_t v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_889_ = ((lean_object*)(l___private_Lean_Meta_DecLevel_0__Lean_Meta_decAux_x3f___closed__3));
v___x_890_ = 0;
v___x_891_ = lean_obj_once(&l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_, &l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_);
v___x_892_ = l_Lean_registerTraceClass(v___x_889_, v___x_890_, v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2____boxed(lean_object* v_a_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l___private_Lean_Meta_DecLevel_0__Lean_Meta_initFn_00___x40_Lean_Meta_DecLevel_3263537904____hygCtx___hyg_2_();
return v_res_894_;
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
