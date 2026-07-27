// Lean compiler output
// Module: Lean.Meta.Sym.Simp.CongrInfo
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.FunInfo import Init.Omega
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Meta_instBEqCongrArgKind_beq(uint8_t, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getCongrSimpKinds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_mkCongrSimpCore_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0(uint8_t, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCongrInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCongrInfo___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCongrInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCongrInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__0_value;
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fixedPrefix "};
static const lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "interlaced "};
static const lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "congrTheorem "};
static const lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_instToMessageDataCongrInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_instToMessageDataCongrInfo___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_instToMessageDataCongrInfo___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_instToMessageDataCongrInfo = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_instToMessageDataCongrInfo___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq(lean_object* v_argKinds_1_, lean_object* v_pre_2_, lean_object* v_i_3_){
_start:
{
lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_4_ = lean_array_get_size(v_argKinds_1_);
v___x_5_ = lean_nat_dec_lt(v_i_3_, v___x_4_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; 
lean_dec(v_i_3_);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v_pre_2_);
return v___x_6_;
}
else
{
lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_7_ = lean_array_fget_borrowed(v_argKinds_1_, v_i_3_);
v___x_8_ = lean_unbox(v___x_7_);
switch(v___x_8_)
{
case 0:
{
lean_object* v___x_9_; 
lean_dec(v_i_3_);
lean_dec(v_pre_2_);
v___x_9_ = lean_box(0);
return v___x_9_;
}
case 2:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_unsigned_to_nat(1u);
v___x_11_ = lean_nat_add(v_i_3_, v___x_10_);
lean_dec(v_i_3_);
v_i_3_ = v___x_11_;
goto _start;
}
default: 
{
lean_object* v___x_13_; 
lean_dec(v_i_3_);
lean_dec(v_pre_2_);
v___x_13_ = lean_box(0);
return v___x_13_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq___boxed(lean_object* v_argKinds_14_, lean_object* v_pre_15_, lean_object* v_i_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq(v_argKinds_14_, v_pre_15_, v_i_16_);
lean_dec_ref(v_argKinds_14_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter___redArg(uint8_t v_x_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_, lean_object* v_h__3_21_){
_start:
{
switch(v_x_18_)
{
case 0:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
lean_dec(v_h__3_21_);
lean_dec(v_h__2_20_);
v___x_22_ = lean_box(0);
v___x_23_ = lean_apply_1(v_h__1_19_, v___x_22_);
return v___x_23_;
}
case 2:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
lean_dec(v_h__3_21_);
lean_dec(v_h__1_19_);
v___x_24_ = lean_box(0);
v___x_25_ = lean_apply_1(v_h__2_20_, v___x_24_);
return v___x_25_;
}
default: 
{
lean_object* v___x_26_; lean_object* v___x_27_; 
lean_dec(v_h__2_20_);
lean_dec(v_h__1_19_);
v___x_26_ = lean_box(v_x_18_);
v___x_27_ = lean_apply_3(v_h__3_21_, v___x_26_, lean_box(0), lean_box(0));
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter___redArg___boxed(lean_object* v_x_28_, lean_object* v_h__1_29_, lean_object* v_h__2_30_, lean_object* v_h__3_31_){
_start:
{
uint8_t v_x_22__boxed_32_; lean_object* v_res_33_; 
v_x_22__boxed_32_ = lean_unbox(v_x_28_);
v_res_33_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter___redArg(v_x_22__boxed_32_, v_h__1_29_, v_h__2_30_, v_h__3_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter(lean_object* v_motive_34_, uint8_t v_x_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_, lean_object* v_h__3_38_){
_start:
{
switch(v_x_35_)
{
case 0:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
lean_dec(v_h__3_38_);
lean_dec(v_h__2_37_);
v___x_39_ = lean_box(0);
v___x_40_ = lean_apply_1(v_h__1_36_, v___x_39_);
return v___x_40_;
}
case 2:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
lean_dec(v_h__3_38_);
lean_dec(v_h__1_36_);
v___x_41_ = lean_box(0);
v___x_42_ = lean_apply_1(v_h__2_37_, v___x_41_);
return v___x_42_;
}
default: 
{
lean_object* v___x_43_; lean_object* v___x_44_; 
lean_dec(v_h__2_37_);
lean_dec(v_h__1_36_);
v___x_43_ = lean_box(v_x_35_);
v___x_44_ = lean_apply_3(v_h__3_38_, v___x_43_, lean_box(0), lean_box(0));
return v___x_44_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter___boxed(lean_object* v_motive_45_, lean_object* v_x_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_, lean_object* v_h__3_49_){
_start:
{
uint8_t v_x_37__boxed_50_; lean_object* v_res_51_; 
v_x_37__boxed_50_ = lean_unbox(v_x_46_);
v_res_51_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter(v_motive_45_, v_x_37__boxed_50_, v_h__1_47_, v_h__2_48_, v_h__3_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_go(lean_object* v_argKinds_52_, lean_object* v_i_53_){
_start:
{
lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_54_ = lean_array_get_size(v_argKinds_52_);
v___x_55_ = lean_nat_dec_lt(v_i_53_, v___x_54_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; 
lean_dec(v_i_53_);
v___x_56_ = lean_box(0);
return v___x_56_;
}
else
{
lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_57_ = lean_array_fget_borrowed(v_argKinds_52_, v_i_53_);
v___x_58_ = lean_unbox(v___x_57_);
switch(v___x_58_)
{
case 0:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_unsigned_to_nat(1u);
v___x_60_ = lean_nat_add(v_i_53_, v___x_59_);
lean_dec(v_i_53_);
v_i_53_ = v___x_60_;
goto _start;
}
case 2:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_unsigned_to_nat(1u);
v___x_63_ = lean_nat_add(v_i_53_, v___x_62_);
v___x_64_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq(v_argKinds_52_, v_i_53_, v___x_63_);
return v___x_64_;
}
default: 
{
lean_object* v___x_65_; 
lean_dec(v_i_53_);
v___x_65_ = lean_box(0);
return v___x_65_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_go___boxed(lean_object* v_argKinds_66_, lean_object* v_i_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_go(v_argKinds_66_, v_i_67_);
lean_dec_ref(v_argKinds_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f(lean_object* v_argKinds_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_go(v_argKinds_69_, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f___boxed(lean_object* v_argKinds_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f(v_argKinds_72_);
lean_dec_ref(v_argKinds_72_);
return v_res_73_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg(lean_object* v_xs_74_, lean_object* v_ys_75_, lean_object* v_x_76_){
_start:
{
lean_object* v_zero_77_; uint8_t v_isZero_78_; 
v_zero_77_ = lean_unsigned_to_nat(0u);
v_isZero_78_ = lean_nat_dec_eq(v_x_76_, v_zero_77_);
if (v_isZero_78_ == 1)
{
lean_dec(v_x_76_);
return v_isZero_78_;
}
else
{
lean_object* v_one_79_; lean_object* v_n_80_; lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; uint8_t v___x_84_; uint8_t v___x_85_; 
v_one_79_ = lean_unsigned_to_nat(1u);
v_n_80_ = lean_nat_sub(v_x_76_, v_one_79_);
lean_dec(v_x_76_);
v___x_81_ = lean_array_fget_borrowed(v_xs_74_, v_n_80_);
v___x_82_ = lean_array_fget_borrowed(v_ys_75_, v_n_80_);
v___x_83_ = lean_unbox(v___x_81_);
v___x_84_ = lean_unbox(v___x_82_);
v___x_85_ = l_Lean_Meta_instBEqCongrArgKind_beq(v___x_83_, v___x_84_);
if (v___x_85_ == 0)
{
lean_dec(v_n_80_);
return v___x_85_;
}
else
{
v_x_76_ = v_n_80_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg___boxed(lean_object* v_xs_87_, lean_object* v_ys_88_, lean_object* v_x_89_){
_start:
{
uint8_t v_res_90_; lean_object* v_r_91_; 
v_res_90_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg(v_xs_87_, v_ys_88_, v_x_89_);
lean_dec_ref(v_ys_88_);
lean_dec_ref(v_xs_87_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0(uint8_t v___y_92_, uint8_t v_a_93_, lean_object* v_as_94_, size_t v_i_95_, size_t v_stop_96_){
_start:
{
uint8_t v___x_97_; 
v___x_97_ = lean_usize_dec_eq(v_i_95_, v_stop_96_);
if (v___x_97_ == 0)
{
uint8_t v___x_98_; uint8_t v___y_100_; lean_object* v___x_104_; uint8_t v___x_105_; uint8_t v___x_106_; uint8_t v___x_107_; 
v___x_98_ = 1;
v___x_104_ = lean_array_uget_borrowed(v_as_94_, v_i_95_);
v___x_105_ = 0;
v___x_106_ = lean_unbox(v___x_104_);
v___x_107_ = l_Lean_Meta_instBEqCongrArgKind_beq(v___x_106_, v___x_105_);
if (v___x_107_ == 0)
{
v___y_100_ = v___y_92_;
goto v___jp_99_;
}
else
{
v___y_100_ = v_a_93_;
goto v___jp_99_;
}
v___jp_99_:
{
if (v___y_100_ == 0)
{
size_t v___x_101_; size_t v___x_102_; 
v___x_101_ = ((size_t)1ULL);
v___x_102_ = lean_usize_add(v_i_95_, v___x_101_);
v_i_95_ = v___x_102_;
goto _start;
}
else
{
return v___x_98_;
}
}
}
else
{
uint8_t v___x_108_; 
v___x_108_ = 0;
return v___x_108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0___boxed(lean_object* v___y_109_, lean_object* v_a_110_, lean_object* v_as_111_, lean_object* v_i_112_, lean_object* v_stop_113_){
_start:
{
uint8_t v___y_7889__boxed_114_; uint8_t v_a_7890__boxed_115_; size_t v_i_boxed_116_; size_t v_stop_boxed_117_; uint8_t v_res_118_; lean_object* v_r_119_; 
v___y_7889__boxed_114_ = lean_unbox(v___y_109_);
v_a_7890__boxed_115_ = lean_unbox(v_a_110_);
v_i_boxed_116_ = lean_unbox_usize(v_i_112_);
lean_dec(v_i_112_);
v_stop_boxed_117_ = lean_unbox_usize(v_stop_113_);
lean_dec(v_stop_113_);
v_res_118_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0(v___y_7889__boxed_114_, v_a_7890__boxed_115_, v_as_111_, v_i_boxed_116_, v_stop_boxed_117_);
lean_dec_ref(v_as_111_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1(size_t v_sz_120_, size_t v_i_121_, lean_object* v_bs_122_){
_start:
{
uint8_t v___x_123_; 
v___x_123_ = lean_usize_dec_lt(v_i_121_, v_sz_120_);
if (v___x_123_ == 0)
{
return v_bs_122_;
}
else
{
lean_object* v_v_124_; lean_object* v___x_125_; lean_object* v_bs_x27_126_; uint8_t v___x_127_; uint8_t v___x_128_; uint8_t v___x_129_; size_t v___x_130_; size_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_v_124_ = lean_array_uget(v_bs_122_, v_i_121_);
v___x_125_ = lean_unsigned_to_nat(0u);
v_bs_x27_126_ = lean_array_uset(v_bs_122_, v_i_121_, v___x_125_);
v___x_127_ = 2;
v___x_128_ = lean_unbox(v_v_124_);
lean_dec(v_v_124_);
v___x_129_ = l_Lean_Meta_instBEqCongrArgKind_beq(v___x_128_, v___x_127_);
v___x_130_ = ((size_t)1ULL);
v___x_131_ = lean_usize_add(v_i_121_, v___x_130_);
v___x_132_ = lean_box(v___x_129_);
v___x_133_ = lean_array_uset(v_bs_x27_126_, v_i_121_, v___x_132_);
v_i_121_ = v___x_131_;
v_bs_122_ = v___x_133_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1___boxed(lean_object* v_sz_135_, lean_object* v_i_136_, lean_object* v_bs_137_){
_start:
{
size_t v_sz_boxed_138_; size_t v_i_boxed_139_; lean_object* v_res_140_; 
v_sz_boxed_138_ = lean_unbox_usize(v_sz_135_);
lean_dec(v_sz_135_);
v_i_boxed_139_ = lean_unbox_usize(v_i_136_);
lean_dec(v_i_136_);
v_res_140_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1(v_sz_boxed_138_, v_i_boxed_139_, v_bs_137_);
return v_res_140_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2(uint8_t v_a_141_, lean_object* v_as_142_, size_t v_i_143_, size_t v_stop_144_){
_start:
{
uint8_t v___x_145_; 
v___x_145_ = lean_usize_dec_eq(v_i_143_, v_stop_144_);
if (v___x_145_ == 0)
{
uint8_t v___x_146_; uint8_t v___y_148_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_146_ = 1;
v___x_152_ = lean_array_uget_borrowed(v_as_142_, v_i_143_);
v___x_153_ = lean_unbox(v___x_152_);
switch(v___x_153_)
{
case 0:
{
v___y_148_ = v_a_141_;
goto v___jp_147_;
}
case 2:
{
v___y_148_ = v_a_141_;
goto v___jp_147_;
}
default: 
{
return v___x_146_;
}
}
v___jp_147_:
{
if (v___y_148_ == 0)
{
size_t v___x_149_; size_t v___x_150_; 
v___x_149_ = ((size_t)1ULL);
v___x_150_ = lean_usize_add(v_i_143_, v___x_149_);
v_i_143_ = v___x_150_;
goto _start;
}
else
{
return v___x_146_;
}
}
}
else
{
uint8_t v___x_154_; 
v___x_154_ = 0;
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2___boxed(lean_object* v_a_155_, lean_object* v_as_156_, lean_object* v_i_157_, lean_object* v_stop_158_){
_start:
{
uint8_t v_a_7939__boxed_159_; size_t v_i_boxed_160_; size_t v_stop_boxed_161_; uint8_t v_res_162_; lean_object* v_r_163_; 
v_a_7939__boxed_159_ = lean_unbox(v_a_155_);
v_i_boxed_160_ = lean_unbox_usize(v_i_157_);
lean_dec(v_i_157_);
v_stop_boxed_161_ = lean_unbox_usize(v_stop_158_);
lean_dec(v_stop_158_);
v_res_162_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2(v_a_7939__boxed_159_, v_as_156_, v_i_boxed_160_, v_stop_boxed_161_);
lean_dec_ref(v_as_156_);
v_r_163_ = lean_box(v_res_162_);
return v_r_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(lean_object* v_f_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v___x_170_; 
lean_inc_ref(v_f_164_);
v___x_170_ = l_Lean_Meta_isProof(v_f_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_307_; 
v_a_171_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_307_ == 0)
{
v___x_173_ = v___x_170_;
v_isShared_174_ = v_isSharedCheck_307_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_170_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_307_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
uint8_t v___x_175_; 
v___x_175_ = lean_unbox(v_a_171_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; 
lean_del_object(v___x_173_);
v___x_176_ = lean_box(0);
lean_inc_ref(v_f_164_);
v___x_177_ = l_Lean_Meta_getFunInfo(v_f_164_, v___x_176_, v_a_165_, v_a_166_, v_a_167_, v_a_168_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_294_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_294_ == 0)
{
v___x_180_ = v___x_177_;
v_isShared_181_ = v_isSharedCheck_294_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_294_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; 
lean_inc_ref(v_f_164_);
v___x_182_ = l_Lean_Meta_getCongrSimpKinds(v_f_164_, v_a_178_, v_a_165_, v_a_166_, v_a_167_, v_a_168_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_285_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_285_ == 0)
{
v___x_185_ = v___x_182_;
v_isShared_186_ = v_isSharedCheck_285_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_182_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_285_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___y_195_; uint8_t v___x_214_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___y_219_; 
v___x_192_ = lean_unsigned_to_nat(0u);
v___x_193_ = lean_array_get_size(v_a_183_);
v___x_214_ = lean_nat_dec_lt(v___x_192_, v___x_193_);
if (v___x_214_ == 0)
{
uint8_t v___x_249_; 
lean_dec(v_a_178_);
lean_dec_ref(v_f_164_);
v___x_249_ = 1;
v___y_195_ = v___x_249_;
goto v___jp_194_;
}
else
{
if (v___x_214_ == 0)
{
lean_dec(v_a_178_);
lean_dec_ref(v_f_164_);
v___y_195_ = v___x_214_;
goto v___jp_194_;
}
else
{
size_t v___x_250_; size_t v___x_251_; uint8_t v___x_252_; uint8_t v___x_253_; 
v___x_250_ = ((size_t)0ULL);
v___x_251_ = lean_usize_of_nat(v___x_193_);
v___x_252_ = lean_unbox(v_a_171_);
v___x_253_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2(v___x_252_, v_a_183_, v___x_250_, v___x_251_);
if (v___x_253_ == 0)
{
lean_dec(v_a_178_);
lean_dec_ref(v_f_164_);
v___y_195_ = v___x_214_;
goto v___jp_194_;
}
else
{
lean_del_object(v___x_185_);
lean_del_object(v___x_180_);
lean_dec(v_a_171_);
if (lean_obj_tag(v_f_164_) == 4)
{
lean_object* v_declName_254_; lean_object* v_us_255_; lean_object* v___x_256_; 
v_declName_254_ = lean_ctor_get(v_f_164_, 0);
v_us_255_ = lean_ctor_get(v_f_164_, 1);
lean_inc(v_us_255_);
lean_inc(v_declName_254_);
v___x_256_ = l_Lean_Meta_mkCongrSimpForConst_x3f(v_declName_254_, v_us_255_, v_a_165_, v_a_166_, v_a_167_, v_a_168_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_276_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_276_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_276_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_276_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
if (lean_obj_tag(v_a_257_) == 1)
{
lean_object* v_val_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_275_; 
v_val_261_ = lean_ctor_get(v_a_257_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v_a_257_);
if (v_isSharedCheck_275_ == 0)
{
v___x_263_ = v_a_257_;
v_isShared_264_ = v_isSharedCheck_275_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_val_261_);
lean_dec(v_a_257_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_275_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v_argKinds_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v_argKinds_265_ = lean_ctor_get(v_val_261_, 2);
v___x_266_ = lean_array_get_size(v_argKinds_265_);
v___x_267_ = lean_nat_dec_eq(v___x_266_, v___x_193_);
if (v___x_267_ == 0)
{
lean_del_object(v___x_263_);
lean_dec(v_val_261_);
lean_del_object(v___x_259_);
v___y_216_ = v_a_165_;
v___y_217_ = v_a_166_;
v___y_218_ = v_a_167_;
v___y_219_ = v_a_168_;
goto v___jp_215_;
}
else
{
uint8_t v___x_268_; 
v___x_268_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg(v_argKinds_265_, v_a_183_, v___x_266_);
if (v___x_268_ == 0)
{
lean_del_object(v___x_263_);
lean_dec(v_val_261_);
lean_del_object(v___x_259_);
v___y_216_ = v_a_165_;
v___y_217_ = v_a_166_;
v___y_218_ = v_a_167_;
v___y_219_ = v_a_168_;
goto v___jp_215_;
}
else
{
lean_object* v___x_270_; 
lean_dec_ref_known(v_f_164_, 2);
lean_dec(v_a_183_);
lean_dec(v_a_178_);
if (v_isShared_264_ == 0)
{
lean_ctor_set_tag(v___x_263_, 3);
v___x_270_ = v___x_263_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_val_261_);
v___x_270_ = v_reuseFailAlloc_274_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
lean_object* v___x_272_; 
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_270_);
v___x_272_ = v___x_259_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_259_);
lean_dec(v_a_257_);
v___y_216_ = v_a_165_;
v___y_217_ = v_a_166_;
v___y_218_ = v_a_167_;
v___y_219_ = v_a_168_;
goto v___jp_215_;
}
}
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
lean_dec_ref_known(v_f_164_, 2);
lean_dec(v_a_183_);
lean_dec(v_a_178_);
v_a_277_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_256_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_256_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
else
{
v___y_216_ = v_a_165_;
v___y_217_ = v_a_166_;
v___y_218_ = v_a_167_;
v___y_219_ = v_a_168_;
goto v___jp_215_;
}
}
}
}
v___jp_187_:
{
lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_188_ = lean_box(0);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_188_);
v___x_190_ = v___x_185_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
v___jp_194_:
{
uint8_t v___x_196_; 
v___x_196_ = lean_nat_dec_lt(v___x_192_, v___x_193_);
if (v___x_196_ == 0)
{
lean_dec(v_a_183_);
lean_del_object(v___x_180_);
lean_dec(v_a_171_);
goto v___jp_187_;
}
else
{
if (v___x_196_ == 0)
{
lean_dec(v_a_183_);
lean_del_object(v___x_180_);
lean_dec(v_a_171_);
goto v___jp_187_;
}
else
{
size_t v___x_197_; size_t v___x_198_; uint8_t v___x_199_; uint8_t v___x_200_; 
v___x_197_ = ((size_t)0ULL);
v___x_198_ = lean_usize_of_nat(v___x_193_);
v___x_199_ = lean_unbox(v_a_171_);
lean_dec(v_a_171_);
v___x_200_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0(v___y_195_, v___x_199_, v_a_183_, v___x_197_, v___x_198_);
if (v___x_200_ == 0)
{
lean_dec(v_a_183_);
lean_del_object(v___x_180_);
goto v___jp_187_;
}
else
{
lean_object* v___x_201_; 
lean_del_object(v___x_185_);
v___x_201_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f(v_a_183_);
if (lean_obj_tag(v___x_201_) == 1)
{
lean_object* v_val_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_206_; 
lean_dec(v_a_183_);
v_val_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_val_202_);
lean_dec_ref_known(v___x_201_, 1);
v___x_203_ = lean_nat_sub(v___x_193_, v_val_202_);
v___x_204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_204_, 0, v_val_202_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_204_);
v___x_206_ = v___x_180_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_204_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
else
{
size_t v_sz_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_212_; 
lean_dec(v___x_201_);
v_sz_208_ = lean_array_size(v_a_183_);
v___x_209_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1(v_sz_208_, v___x_197_, v_a_183_);
v___x_210_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_210_);
v___x_212_ = v___x_180_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_210_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
}
}
v___jp_215_:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Meta_mkCongrSimpCore_x3f(v_f_164_, v_a_178_, v_a_183_, v___x_214_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_240_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_240_ == 0)
{
v___x_223_ = v___x_220_;
v_isShared_224_ = v_isSharedCheck_240_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_220_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_240_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
if (lean_obj_tag(v_a_221_) == 1)
{
lean_object* v_val_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_235_; 
v_val_225_ = lean_ctor_get(v_a_221_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v_a_221_);
if (v_isSharedCheck_235_ == 0)
{
v___x_227_ = v_a_221_;
v_isShared_228_ = v_isSharedCheck_235_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_val_225_);
lean_dec(v_a_221_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_235_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
lean_ctor_set_tag(v___x_227_, 3);
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_val_225_);
v___x_230_ = v_reuseFailAlloc_234_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_232_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_230_);
v___x_232_ = v___x_223_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
else
{
lean_object* v___x_236_; lean_object* v___x_238_; 
lean_dec(v_a_221_);
v___x_236_ = lean_box(0);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_236_);
v___x_238_ = v___x_223_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
else
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_248_; 
v_a_241_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v___x_220_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_220_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_241_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_del_object(v___x_180_);
lean_dec(v_a_178_);
lean_dec(v_a_171_);
lean_dec_ref(v_f_164_);
v_a_286_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_182_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_182_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
lean_dec(v_a_171_);
lean_dec_ref(v_f_164_);
v_a_295_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___x_177_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_177_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
else
{
lean_object* v___x_303_; lean_object* v___x_305_; 
lean_dec(v_a_171_);
lean_dec_ref(v_f_164_);
v___x_303_ = lean_box(0);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 0, v___x_303_);
v___x_305_ = v___x_173_;
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
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_dec_ref(v_f_164_);
v_a_308_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_170_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_170_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg___boxed(lean_object* v_f_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(v_f_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo(lean_object* v_f_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(v_f_323_, v_a_326_, v_a_327_, v_a_328_, v_a_329_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___boxed(lean_object* v_f_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo(v_f_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
return v_res_340_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3(lean_object* v_xs_341_, lean_object* v_ys_342_, lean_object* v_hsz_343_, lean_object* v_x_344_, lean_object* v_x_345_){
_start:
{
uint8_t v___x_346_; 
v___x_346_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg(v_xs_341_, v_ys_342_, v_x_344_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___boxed(lean_object* v_xs_347_, lean_object* v_ys_348_, lean_object* v_hsz_349_, lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
uint8_t v_res_352_; lean_object* v_r_353_; 
v_res_352_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3(v_xs_347_, v_ys_348_, v_hsz_349_, v_x_350_, v_x_351_);
lean_dec_ref(v_ys_348_);
lean_dec_ref(v_xs_347_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_354_, lean_object* v_x_355_, lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
lean_object* v_ks_358_; lean_object* v_vs_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_385_; 
v_ks_358_ = lean_ctor_get(v_x_354_, 0);
v_vs_359_ = lean_ctor_get(v_x_354_, 1);
v_isSharedCheck_385_ = !lean_is_exclusive(v_x_354_);
if (v_isSharedCheck_385_ == 0)
{
v___x_361_ = v_x_354_;
v_isShared_362_ = v_isSharedCheck_385_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_vs_359_);
lean_inc(v_ks_358_);
lean_dec(v_x_354_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_385_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_363_ = lean_array_get_size(v_ks_358_);
v___x_364_ = lean_nat_dec_lt(v_x_355_, v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
lean_dec(v_x_355_);
v___x_365_ = lean_array_push(v_ks_358_, v_x_356_);
v___x_366_ = lean_array_push(v_vs_359_, v_x_357_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 1, v___x_366_);
lean_ctor_set(v___x_361_, 0, v___x_365_);
v___x_368_ = v___x_361_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
else
{
lean_object* v_k_x27_370_; size_t v___x_371_; size_t v___x_372_; uint8_t v___x_373_; 
v_k_x27_370_ = lean_array_fget_borrowed(v_ks_358_, v_x_355_);
v___x_371_ = lean_ptr_addr(v_x_356_);
v___x_372_ = lean_ptr_addr(v_k_x27_370_);
v___x_373_ = lean_usize_dec_eq(v___x_371_, v___x_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_375_; 
if (v_isShared_362_ == 0)
{
v___x_375_ = v___x_361_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_ks_358_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_vs_359_);
v___x_375_ = v_reuseFailAlloc_379_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_unsigned_to_nat(1u);
v___x_377_ = lean_nat_add(v_x_355_, v___x_376_);
lean_dec(v_x_355_);
v_x_354_ = v___x_375_;
v_x_355_ = v___x_377_;
goto _start;
}
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_380_ = lean_array_fset(v_ks_358_, v_x_355_, v_x_356_);
v___x_381_ = lean_array_fset(v_vs_359_, v_x_355_, v_x_357_);
lean_dec(v_x_355_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 1, v___x_381_);
lean_ctor_set(v___x_361_, 0, v___x_380_);
v___x_383_ = v___x_361_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4___redArg(lean_object* v_n_386_, lean_object* v_k_387_, lean_object* v_v_388_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_unsigned_to_nat(0u);
v___x_390_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5___redArg(v_n_386_, v___x_389_, v_k_387_, v_v_388_);
return v___x_390_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(lean_object* v_x_392_, size_t v_x_393_, size_t v_x_394_, lean_object* v_x_395_, lean_object* v_x_396_){
_start:
{
if (lean_obj_tag(v_x_392_) == 0)
{
lean_object* v_es_397_; size_t v___x_398_; size_t v___x_399_; lean_object* v_j_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v_es_397_ = lean_ctor_get(v_x_392_, 0);
v___x_398_ = ((size_t)31ULL);
v___x_399_ = lean_usize_land(v_x_393_, v___x_398_);
v_j_400_ = lean_usize_to_nat(v___x_399_);
v___x_401_ = lean_array_get_size(v_es_397_);
v___x_402_ = lean_nat_dec_lt(v_j_400_, v___x_401_);
if (v___x_402_ == 0)
{
lean_dec(v_j_400_);
lean_dec(v_x_396_);
lean_dec_ref(v_x_395_);
return v_x_392_;
}
else
{
lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_443_; 
lean_inc_ref(v_es_397_);
v_isSharedCheck_443_ = !lean_is_exclusive(v_x_392_);
if (v_isSharedCheck_443_ == 0)
{
lean_object* v_unused_444_; 
v_unused_444_ = lean_ctor_get(v_x_392_, 0);
lean_dec(v_unused_444_);
v___x_404_ = v_x_392_;
v_isShared_405_ = v_isSharedCheck_443_;
goto v_resetjp_403_;
}
else
{
lean_dec(v_x_392_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_443_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v_v_406_; lean_object* v___x_407_; lean_object* v_xs_x27_408_; lean_object* v___y_410_; 
v_v_406_ = lean_array_fget(v_es_397_, v_j_400_);
v___x_407_ = lean_box(0);
v_xs_x27_408_ = lean_array_fset(v_es_397_, v_j_400_, v___x_407_);
switch(lean_obj_tag(v_v_406_))
{
case 0:
{
lean_object* v_key_415_; lean_object* v_val_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_428_; 
v_key_415_ = lean_ctor_get(v_v_406_, 0);
v_val_416_ = lean_ctor_get(v_v_406_, 1);
v_isSharedCheck_428_ = !lean_is_exclusive(v_v_406_);
if (v_isSharedCheck_428_ == 0)
{
v___x_418_ = v_v_406_;
v_isShared_419_ = v_isSharedCheck_428_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_val_416_);
lean_inc(v_key_415_);
lean_dec(v_v_406_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_428_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
size_t v___x_420_; size_t v___x_421_; uint8_t v___x_422_; 
v___x_420_ = lean_ptr_addr(v_x_395_);
v___x_421_ = lean_ptr_addr(v_key_415_);
v___x_422_ = lean_usize_dec_eq(v___x_420_, v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; 
lean_del_object(v___x_418_);
v___x_423_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_415_, v_val_416_, v_x_395_, v_x_396_);
v___x_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
v___y_410_ = v___x_424_;
goto v___jp_409_;
}
else
{
lean_object* v___x_426_; 
lean_dec(v_val_416_);
lean_dec(v_key_415_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 1, v_x_396_);
lean_ctor_set(v___x_418_, 0, v_x_395_);
v___x_426_ = v___x_418_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_x_395_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_x_396_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
v___y_410_ = v___x_426_;
goto v___jp_409_;
}
}
}
}
case 1:
{
lean_object* v_node_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_441_; 
v_node_429_ = lean_ctor_get(v_v_406_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v_v_406_);
if (v_isSharedCheck_441_ == 0)
{
v___x_431_ = v_v_406_;
v_isShared_432_ = v_isSharedCheck_441_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_node_429_);
lean_dec(v_v_406_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_441_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
size_t v___x_433_; size_t v___x_434_; size_t v___x_435_; size_t v___x_436_; lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_433_ = ((size_t)5ULL);
v___x_434_ = lean_usize_shift_right(v_x_393_, v___x_433_);
v___x_435_ = ((size_t)1ULL);
v___x_436_ = lean_usize_add(v_x_394_, v___x_435_);
v___x_437_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_node_429_, v___x_434_, v___x_436_, v_x_395_, v_x_396_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_437_);
v___x_439_ = v___x_431_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
v___y_410_ = v___x_439_;
goto v___jp_409_;
}
}
}
default: 
{
lean_object* v___x_442_; 
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v_x_395_);
lean_ctor_set(v___x_442_, 1, v_x_396_);
v___y_410_ = v___x_442_;
goto v___jp_409_;
}
}
v___jp_409_:
{
lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_411_ = lean_array_fset(v_xs_x27_408_, v_j_400_, v___y_410_);
lean_dec(v_j_400_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_411_);
v___x_413_ = v___x_404_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
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
else
{
lean_object* v_ks_445_; lean_object* v_vs_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_466_; 
v_ks_445_ = lean_ctor_get(v_x_392_, 0);
v_vs_446_ = lean_ctor_get(v_x_392_, 1);
v_isSharedCheck_466_ = !lean_is_exclusive(v_x_392_);
if (v_isSharedCheck_466_ == 0)
{
v___x_448_ = v_x_392_;
v_isShared_449_ = v_isSharedCheck_466_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_vs_446_);
lean_inc(v_ks_445_);
lean_dec(v_x_392_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_466_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_ks_445_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_vs_446_);
v___x_451_ = v_reuseFailAlloc_465_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v_newNode_452_; uint8_t v___y_454_; size_t v___x_460_; uint8_t v___x_461_; 
v_newNode_452_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4___redArg(v___x_451_, v_x_395_, v_x_396_);
v___x_460_ = ((size_t)7ULL);
v___x_461_ = lean_usize_dec_le(v___x_460_, v_x_394_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_462_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_452_);
v___x_463_ = lean_unsigned_to_nat(4u);
v___x_464_ = lean_nat_dec_lt(v___x_462_, v___x_463_);
lean_dec(v___x_462_);
v___y_454_ = v___x_464_;
goto v___jp_453_;
}
else
{
v___y_454_ = v___x_461_;
goto v___jp_453_;
}
v___jp_453_:
{
if (v___y_454_ == 0)
{
lean_object* v_ks_455_; lean_object* v_vs_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v_ks_455_ = lean_ctor_get(v_newNode_452_, 0);
lean_inc_ref(v_ks_455_);
v_vs_456_ = lean_ctor_get(v_newNode_452_, 1);
lean_inc_ref(v_vs_456_);
lean_dec_ref(v_newNode_452_);
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0);
v___x_459_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(v_x_394_, v_ks_455_, v_vs_456_, v___x_457_, v___x_458_);
lean_dec_ref(v_vs_456_);
lean_dec_ref(v_ks_455_);
return v___x_459_;
}
else
{
return v_newNode_452_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(size_t v_depth_467_, lean_object* v_keys_468_, lean_object* v_vals_469_, lean_object* v_i_470_, lean_object* v_entries_471_){
_start:
{
lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_472_ = lean_array_get_size(v_keys_468_);
v___x_473_ = lean_nat_dec_lt(v_i_470_, v___x_472_);
if (v___x_473_ == 0)
{
lean_dec(v_i_470_);
return v_entries_471_;
}
else
{
lean_object* v_k_474_; lean_object* v_v_475_; size_t v___x_476_; size_t v___x_477_; size_t v___x_478_; uint64_t v___x_479_; size_t v_h_480_; size_t v___x_481_; lean_object* v___x_482_; size_t v___x_483_; size_t v___x_484_; size_t v___x_485_; size_t v_h_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_k_474_ = lean_array_fget_borrowed(v_keys_468_, v_i_470_);
v_v_475_ = lean_array_fget_borrowed(v_vals_469_, v_i_470_);
v___x_476_ = lean_ptr_addr(v_k_474_);
v___x_477_ = ((size_t)3ULL);
v___x_478_ = lean_usize_shift_right(v___x_476_, v___x_477_);
v___x_479_ = lean_usize_to_uint64(v___x_478_);
v_h_480_ = lean_uint64_to_usize(v___x_479_);
v___x_481_ = ((size_t)5ULL);
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = ((size_t)1ULL);
v___x_484_ = lean_usize_sub(v_depth_467_, v___x_483_);
v___x_485_ = lean_usize_mul(v___x_481_, v___x_484_);
v_h_486_ = lean_usize_shift_right(v_h_480_, v___x_485_);
v___x_487_ = lean_nat_add(v_i_470_, v___x_482_);
lean_dec(v_i_470_);
lean_inc(v_v_475_);
lean_inc(v_k_474_);
v___x_488_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_entries_471_, v_h_486_, v_depth_467_, v_k_474_, v_v_475_);
v_i_470_ = v___x_487_;
v_entries_471_ = v___x_488_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_490_, lean_object* v_keys_491_, lean_object* v_vals_492_, lean_object* v_i_493_, lean_object* v_entries_494_){
_start:
{
size_t v_depth_boxed_495_; lean_object* v_res_496_; 
v_depth_boxed_495_ = lean_unbox_usize(v_depth_490_);
lean_dec(v_depth_490_);
v_res_496_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(v_depth_boxed_495_, v_keys_491_, v_vals_492_, v_i_493_, v_entries_494_);
lean_dec_ref(v_vals_492_);
lean_dec_ref(v_keys_491_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___boxed(lean_object* v_x_497_, lean_object* v_x_498_, lean_object* v_x_499_, lean_object* v_x_500_, lean_object* v_x_501_){
_start:
{
size_t v_x_2500__boxed_502_; size_t v_x_2501__boxed_503_; lean_object* v_res_504_; 
v_x_2500__boxed_502_ = lean_unbox_usize(v_x_498_);
lean_dec(v_x_498_);
v_x_2501__boxed_503_ = lean_unbox_usize(v_x_499_);
lean_dec(v_x_499_);
v_res_504_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_x_497_, v_x_2500__boxed_502_, v_x_2501__boxed_503_, v_x_500_, v_x_501_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1___redArg(lean_object* v_x_505_, lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
size_t v___x_508_; size_t v___x_509_; size_t v___x_510_; uint64_t v___x_511_; size_t v___x_512_; size_t v___x_513_; lean_object* v___x_514_; 
v___x_508_ = lean_ptr_addr(v_x_506_);
v___x_509_ = ((size_t)3ULL);
v___x_510_ = lean_usize_shift_right(v___x_508_, v___x_509_);
v___x_511_ = lean_usize_to_uint64(v___x_510_);
v___x_512_ = lean_uint64_to_usize(v___x_511_);
v___x_513_ = ((size_t)1ULL);
v___x_514_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_x_505_, v___x_512_, v___x_513_, v_x_506_, v_x_507_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_515_, lean_object* v_vals_516_, lean_object* v_i_517_, lean_object* v_k_518_){
_start:
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = lean_array_get_size(v_keys_515_);
v___x_520_ = lean_nat_dec_lt(v_i_517_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; 
lean_dec(v_i_517_);
v___x_521_ = lean_box(0);
return v___x_521_;
}
else
{
lean_object* v_k_x27_522_; size_t v___x_523_; size_t v___x_524_; uint8_t v___x_525_; 
v_k_x27_522_ = lean_array_fget_borrowed(v_keys_515_, v_i_517_);
v___x_523_ = lean_ptr_addr(v_k_518_);
v___x_524_ = lean_ptr_addr(v_k_x27_522_);
v___x_525_ = lean_usize_dec_eq(v___x_523_, v___x_524_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_unsigned_to_nat(1u);
v___x_527_ = lean_nat_add(v_i_517_, v___x_526_);
lean_dec(v_i_517_);
v_i_517_ = v___x_527_;
goto _start;
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_array_fget_borrowed(v_vals_516_, v_i_517_);
lean_dec(v_i_517_);
lean_inc(v___x_529_);
v___x_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_531_, lean_object* v_vals_532_, lean_object* v_i_533_, lean_object* v_k_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(v_keys_531_, v_vals_532_, v_i_533_, v_k_534_);
lean_dec_ref(v_k_534_);
lean_dec_ref(v_vals_532_);
lean_dec_ref(v_keys_531_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(lean_object* v_x_536_, size_t v_x_537_, lean_object* v_x_538_){
_start:
{
if (lean_obj_tag(v_x_536_) == 0)
{
lean_object* v_es_539_; lean_object* v___x_540_; size_t v___x_541_; size_t v___x_542_; lean_object* v_j_543_; lean_object* v___x_544_; 
v_es_539_ = lean_ctor_get(v_x_536_, 0);
v___x_540_ = lean_box(2);
v___x_541_ = ((size_t)31ULL);
v___x_542_ = lean_usize_land(v_x_537_, v___x_541_);
v_j_543_ = lean_usize_to_nat(v___x_542_);
v___x_544_ = lean_array_get_borrowed(v___x_540_, v_es_539_, v_j_543_);
lean_dec(v_j_543_);
switch(lean_obj_tag(v___x_544_))
{
case 0:
{
lean_object* v_key_545_; lean_object* v_val_546_; size_t v___x_547_; size_t v___x_548_; uint8_t v___x_549_; 
v_key_545_ = lean_ctor_get(v___x_544_, 0);
v_val_546_ = lean_ctor_get(v___x_544_, 1);
v___x_547_ = lean_ptr_addr(v_x_538_);
v___x_548_ = lean_ptr_addr(v_key_545_);
v___x_549_ = lean_usize_dec_eq(v___x_547_, v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; 
v___x_550_ = lean_box(0);
return v___x_550_;
}
else
{
lean_object* v___x_551_; 
lean_inc(v_val_546_);
v___x_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_551_, 0, v_val_546_);
return v___x_551_;
}
}
case 1:
{
lean_object* v_node_552_; size_t v___x_553_; size_t v___x_554_; 
v_node_552_ = lean_ctor_get(v___x_544_, 0);
v___x_553_ = ((size_t)5ULL);
v___x_554_ = lean_usize_shift_right(v_x_537_, v___x_553_);
v_x_536_ = v_node_552_;
v_x_537_ = v___x_554_;
goto _start;
}
default: 
{
lean_object* v___x_556_; 
v___x_556_ = lean_box(0);
return v___x_556_;
}
}
}
else
{
lean_object* v_ks_557_; lean_object* v_vs_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v_ks_557_ = lean_ctor_get(v_x_536_, 0);
v_vs_558_ = lean_ctor_get(v_x_536_, 1);
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(v_ks_557_, v_vs_558_, v___x_559_, v_x_538_);
return v___x_560_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg___boxed(lean_object* v_x_561_, lean_object* v_x_562_, lean_object* v_x_563_){
_start:
{
size_t v_x_2705__boxed_564_; lean_object* v_res_565_; 
v_x_2705__boxed_564_ = lean_unbox_usize(v_x_562_);
lean_dec(v_x_562_);
v_res_565_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(v_x_561_, v_x_2705__boxed_564_, v_x_563_);
lean_dec_ref(v_x_563_);
lean_dec_ref(v_x_561_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
size_t v___x_568_; size_t v___x_569_; size_t v___x_570_; uint64_t v___x_571_; size_t v___x_572_; lean_object* v___x_573_; 
v___x_568_ = lean_ptr_addr(v_x_567_);
v___x_569_ = ((size_t)3ULL);
v___x_570_ = lean_usize_shift_right(v___x_568_, v___x_569_);
v___x_571_ = lean_usize_to_uint64(v___x_570_);
v___x_572_ = lean_uint64_to_usize(v___x_571_);
v___x_573_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(v_x_566_, v___x_572_, v_x_567_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg___boxed(lean_object* v_x_574_, lean_object* v_x_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(v_x_574_, v_x_575_);
lean_dec_ref(v_x_575_);
lean_dec_ref(v_x_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCongrInfo___redArg(lean_object* v_f_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___x_584_; lean_object* v_congrInfo_585_; lean_object* v___x_586_; 
v___x_584_ = lean_st_ref_get(v_a_578_);
v_congrInfo_585_ = lean_ctor_get(v___x_584_, 5);
lean_inc_ref(v_congrInfo_585_);
lean_dec(v___x_584_);
v___x_586_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(v_congrInfo_585_, v_f_577_);
lean_dec_ref(v_congrInfo_585_);
if (lean_obj_tag(v___x_586_) == 1)
{
lean_object* v_val_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
lean_dec_ref(v_f_577_);
v_val_587_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_586_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_val_587_);
lean_dec(v___x_586_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set_tag(v___x_589_, 0);
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_val_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
else
{
lean_object* v___x_595_; 
lean_dec(v___x_586_);
lean_inc_ref(v_f_577_);
v___x_595_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(v_f_577_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_625_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_625_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_625_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_625_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v_share_601_; lean_object* v_maxFVar_602_; lean_object* v_proofInstInfo_603_; lean_object* v_inferType_604_; lean_object* v_getLevel_605_; lean_object* v_congrInfo_606_; lean_object* v_defEqI_607_; lean_object* v_extensions_608_; lean_object* v_issues_609_; lean_object* v_canon_610_; lean_object* v_instanceOverrides_611_; uint8_t v_debug_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_624_; 
v___x_600_ = lean_st_ref_take(v_a_578_);
v_share_601_ = lean_ctor_get(v___x_600_, 0);
v_maxFVar_602_ = lean_ctor_get(v___x_600_, 1);
v_proofInstInfo_603_ = lean_ctor_get(v___x_600_, 2);
v_inferType_604_ = lean_ctor_get(v___x_600_, 3);
v_getLevel_605_ = lean_ctor_get(v___x_600_, 4);
v_congrInfo_606_ = lean_ctor_get(v___x_600_, 5);
v_defEqI_607_ = lean_ctor_get(v___x_600_, 6);
v_extensions_608_ = lean_ctor_get(v___x_600_, 7);
v_issues_609_ = lean_ctor_get(v___x_600_, 8);
v_canon_610_ = lean_ctor_get(v___x_600_, 9);
v_instanceOverrides_611_ = lean_ctor_get(v___x_600_, 10);
v_debug_612_ = lean_ctor_get_uint8(v___x_600_, sizeof(void*)*11);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_624_ == 0)
{
v___x_614_ = v___x_600_;
v_isShared_615_ = v_isSharedCheck_624_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_instanceOverrides_611_);
lean_inc(v_canon_610_);
lean_inc(v_issues_609_);
lean_inc(v_extensions_608_);
lean_inc(v_defEqI_607_);
lean_inc(v_congrInfo_606_);
lean_inc(v_getLevel_605_);
lean_inc(v_inferType_604_);
lean_inc(v_proofInstInfo_603_);
lean_inc(v_maxFVar_602_);
lean_inc(v_share_601_);
lean_dec(v___x_600_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_624_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; lean_object* v___x_618_; 
lean_inc(v_a_596_);
v___x_616_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1___redArg(v_congrInfo_606_, v_f_577_, v_a_596_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 5, v___x_616_);
v___x_618_ = v___x_614_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_share_601_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v_maxFVar_602_);
lean_ctor_set(v_reuseFailAlloc_623_, 2, v_proofInstInfo_603_);
lean_ctor_set(v_reuseFailAlloc_623_, 3, v_inferType_604_);
lean_ctor_set(v_reuseFailAlloc_623_, 4, v_getLevel_605_);
lean_ctor_set(v_reuseFailAlloc_623_, 5, v___x_616_);
lean_ctor_set(v_reuseFailAlloc_623_, 6, v_defEqI_607_);
lean_ctor_set(v_reuseFailAlloc_623_, 7, v_extensions_608_);
lean_ctor_set(v_reuseFailAlloc_623_, 8, v_issues_609_);
lean_ctor_set(v_reuseFailAlloc_623_, 9, v_canon_610_);
lean_ctor_set(v_reuseFailAlloc_623_, 10, v_instanceOverrides_611_);
lean_ctor_set_uint8(v_reuseFailAlloc_623_, sizeof(void*)*11, v_debug_612_);
v___x_618_ = v_reuseFailAlloc_623_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v___x_619_; lean_object* v___x_621_; 
v___x_619_ = lean_st_ref_set(v_a_578_, v___x_618_);
if (v_isShared_599_ == 0)
{
v___x_621_ = v___x_598_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_596_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_577_);
return v___x_595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCongrInfo___redArg___boxed(lean_object* v_f_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_Meta_Sym_getCongrInfo___redArg(v_f_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec(v_a_629_);
lean_dec_ref(v_a_628_);
lean_dec(v_a_627_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCongrInfo(lean_object* v_f_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_Meta_Sym_getCongrInfo___redArg(v_f_634_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCongrInfo___boxed(lean_object* v_f_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Meta_Sym_getCongrInfo(v_f_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0(lean_object* v_00_u03b2_652_, lean_object* v_x_653_, lean_object* v_x_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(v_x_653_, v_x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___boxed(lean_object* v_00_u03b2_656_, lean_object* v_x_657_, lean_object* v_x_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0(v_00_u03b2_656_, v_x_657_, v_x_658_);
lean_dec_ref(v_x_658_);
lean_dec_ref(v_x_657_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1(lean_object* v_00_u03b2_660_, lean_object* v_x_661_, lean_object* v_x_662_, lean_object* v_x_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1___redArg(v_x_661_, v_x_662_, v_x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0(lean_object* v_00_u03b2_665_, lean_object* v_x_666_, size_t v_x_667_, lean_object* v_x_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(v_x_666_, v_x_667_, v_x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___boxed(lean_object* v_00_u03b2_670_, lean_object* v_x_671_, lean_object* v_x_672_, lean_object* v_x_673_){
_start:
{
size_t v_x_2857__boxed_674_; lean_object* v_res_675_; 
v_x_2857__boxed_674_ = lean_unbox_usize(v_x_672_);
lean_dec(v_x_672_);
v_res_675_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0(v_00_u03b2_670_, v_x_671_, v_x_2857__boxed_674_, v_x_673_);
lean_dec_ref(v_x_673_);
lean_dec_ref(v_x_671_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2(lean_object* v_00_u03b2_676_, lean_object* v_x_677_, size_t v_x_678_, size_t v_x_679_, lean_object* v_x_680_, lean_object* v_x_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_x_677_, v_x_678_, v_x_679_, v_x_680_, v_x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___boxed(lean_object* v_00_u03b2_683_, lean_object* v_x_684_, lean_object* v_x_685_, lean_object* v_x_686_, lean_object* v_x_687_, lean_object* v_x_688_){
_start:
{
size_t v_x_2868__boxed_689_; size_t v_x_2869__boxed_690_; lean_object* v_res_691_; 
v_x_2868__boxed_689_ = lean_unbox_usize(v_x_685_);
lean_dec(v_x_685_);
v_x_2869__boxed_690_ = lean_unbox_usize(v_x_686_);
lean_dec(v_x_686_);
v_res_691_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2(v_00_u03b2_683_, v_x_684_, v_x_2868__boxed_689_, v_x_2869__boxed_690_, v_x_687_, v_x_688_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_692_, lean_object* v_keys_693_, lean_object* v_vals_694_, lean_object* v_heq_695_, lean_object* v_i_696_, lean_object* v_k_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(v_keys_693_, v_vals_694_, v_i_696_, v_k_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_699_, lean_object* v_keys_700_, lean_object* v_vals_701_, lean_object* v_heq_702_, lean_object* v_i_703_, lean_object* v_k_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1(v_00_u03b2_699_, v_keys_700_, v_vals_701_, v_heq_702_, v_i_703_, v_k_704_);
lean_dec_ref(v_k_704_);
lean_dec_ref(v_vals_701_);
lean_dec_ref(v_keys_700_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_706_, lean_object* v_n_707_, lean_object* v_k_708_, lean_object* v_v_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4___redArg(v_n_707_, v_k_708_, v_v_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_711_, size_t v_depth_712_, lean_object* v_keys_713_, lean_object* v_vals_714_, lean_object* v_heq_715_, lean_object* v_i_716_, lean_object* v_entries_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(v_depth_712_, v_keys_713_, v_vals_714_, v_i_716_, v_entries_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_719_, lean_object* v_depth_720_, lean_object* v_keys_721_, lean_object* v_vals_722_, lean_object* v_heq_723_, lean_object* v_i_724_, lean_object* v_entries_725_){
_start:
{
size_t v_depth_boxed_726_; lean_object* v_res_727_; 
v_depth_boxed_726_ = lean_unbox_usize(v_depth_720_);
lean_dec(v_depth_720_);
v_res_727_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5(v_00_u03b2_719_, v_depth_boxed_726_, v_keys_721_, v_vals_722_, v_heq_723_, v_i_724_, v_entries_725_);
lean_dec_ref(v_vals_722_);
lean_dec_ref(v_keys_721_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_728_, lean_object* v_x_729_, lean_object* v_x_730_, lean_object* v_x_731_, lean_object* v_x_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5___redArg(v_x_729_, v_x_730_, v_x_731_, v_x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0(lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
if (lean_obj_tag(v_a_736_) == 0)
{
lean_object* v___x_738_; 
v___x_738_ = l_List_reverse___redArg(v_a_737_);
return v___x_738_;
}
else
{
lean_object* v_head_739_; lean_object* v_tail_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_755_; 
v_head_739_ = lean_ctor_get(v_a_736_, 0);
v_tail_740_ = lean_ctor_get(v_a_736_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v_a_736_);
if (v_isSharedCheck_755_ == 0)
{
v___x_742_ = v_a_736_;
v_isShared_743_ = v_isSharedCheck_755_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_tail_740_);
lean_inc(v_head_739_);
lean_dec(v_a_736_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_755_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___y_745_; uint8_t v___x_752_; 
v___x_752_ = lean_unbox(v_head_739_);
lean_dec(v_head_739_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; 
v___x_753_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__0));
v___y_745_ = v___x_753_;
goto v___jp_744_;
}
else
{
lean_object* v___x_754_; 
v___x_754_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__1));
v___y_745_ = v___x_754_;
goto v___jp_744_;
}
v___jp_744_:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
lean_inc_ref(v___y_745_);
v___x_746_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_746_, 0, v___y_745_);
v___x_747_ = l_Lean_MessageData_ofFormat(v___x_746_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 1, v_a_737_);
lean_ctor_set(v___x_742_, 0, v___x_747_);
v___x_749_ = v___x_742_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_a_737_);
v___x_749_ = v_reuseFailAlloc_751_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
v_a_736_ = v_tail_740_;
v_a_737_ = v___x_749_;
goto _start;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__1));
v___x_760_ = l_Lean_MessageData_ofFormat(v___x_759_);
return v___x_760_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__3));
v___x_763_ = l_Lean_stringToMessageData(v___x_762_);
return v___x_763_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__5));
v___x_766_ = l_Lean_stringToMessageData(v___x_765_);
return v___x_766_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__7));
v___x_769_ = l_Lean_stringToMessageData(v___x_768_);
return v___x_769_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__9));
v___x_772_ = l_Lean_stringToMessageData(v___x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData(lean_object* v_x_773_){
_start:
{
switch(lean_obj_tag(v_x_773_))
{
case 0:
{
lean_object* v___x_774_; 
v___x_774_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2);
return v___x_774_;
}
case 1:
{
lean_object* v_prefixSize_775_; lean_object* v_suffixSize_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_793_; 
v_prefixSize_775_ = lean_ctor_get(v_x_773_, 0);
v_suffixSize_776_ = lean_ctor_get(v_x_773_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v_x_773_);
if (v_isSharedCheck_793_ == 0)
{
v___x_778_ = v_x_773_;
v_isShared_779_ = v_isSharedCheck_793_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_suffixSize_776_);
lean_inc(v_prefixSize_775_);
lean_dec(v_x_773_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_793_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_780_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4);
v___x_781_ = l_Nat_reprFast(v_prefixSize_775_);
v___x_782_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
v___x_783_ = l_Lean_MessageData_ofFormat(v___x_782_);
if (v_isShared_779_ == 0)
{
lean_ctor_set_tag(v___x_778_, 7);
lean_ctor_set(v___x_778_, 1, v___x_783_);
lean_ctor_set(v___x_778_, 0, v___x_780_);
v___x_785_ = v___x_778_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v___x_783_);
v___x_785_ = v_reuseFailAlloc_792_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_786_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6);
v___x_787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = l_Nat_reprFast(v_suffixSize_776_);
v___x_789_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
v___x_790_ = l_Lean_MessageData_ofFormat(v___x_789_);
v___x_791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_787_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
return v___x_791_;
}
}
}
case 2:
{
lean_object* v_rewritable_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_rewritable_794_ = lean_ctor_get(v_x_773_, 0);
lean_inc_ref(v_rewritable_794_);
lean_dec_ref_known(v_x_773_, 1);
v___x_795_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8);
v___x_796_ = lean_array_to_list(v_rewritable_794_);
v___x_797_ = lean_box(0);
v___x_798_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0(v___x_796_, v___x_797_);
v___x_799_ = l_Lean_MessageData_ofList(v___x_798_);
v___x_800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_795_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
return v___x_800_;
}
default: 
{
lean_object* v_thm_801_; lean_object* v_proof_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_thm_801_ = lean_ctor_get(v_x_773_, 0);
lean_inc_ref(v_thm_801_);
lean_dec_ref_known(v_x_773_, 1);
v_proof_802_ = lean_ctor_get(v_thm_801_, 1);
lean_inc_ref(v_proof_802_);
lean_dec_ref(v_thm_801_);
v___x_803_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10);
v___x_804_ = l_Lean_MessageData_ofExpr(v_proof_802_);
v___x_805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_803_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
return v___x_805_;
}
}
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_FunInfo(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_CongrInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_FunInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_CongrInfo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_FunInfo(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_CongrInfo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_FunInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_CongrInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_CongrInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_CongrInfo(builtin);
}
#ifdef __cplusplus
}
#endif
