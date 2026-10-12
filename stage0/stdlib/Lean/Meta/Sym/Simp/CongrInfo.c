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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
lean_object* l_Lean_Meta_mkCongrSimpCore_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
if (v___x_8_ == 2)
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_unsigned_to_nat(1u);
v___x_10_ = lean_nat_add(v_i_3_, v___x_9_);
lean_dec(v_i_3_);
v_i_3_ = v___x_10_;
goto _start;
}
else
{
lean_object* v___x_12_; 
lean_dec(v_i_3_);
lean_dec(v_pre_2_);
v___x_12_ = lean_box(0);
return v___x_12_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq___boxed(lean_object* v_argKinds_13_, lean_object* v_pre_14_, lean_object* v_i_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq(v_argKinds_13_, v_pre_14_, v_i_15_);
lean_dec_ref(v_argKinds_13_);
return v_res_16_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter___redArg(uint8_t v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_, lean_object* v_h__3_20_){
_start:
{
switch(v_x_17_)
{
case 0:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
lean_dec(v_h__3_20_);
lean_dec(v_h__2_19_);
v___x_21_ = lean_box(0);
v___x_22_ = lean_apply_1(v_h__1_18_, v___x_21_);
return v___x_22_;
}
case 2:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
lean_dec(v_h__3_20_);
lean_dec(v_h__1_18_);
v___x_23_ = lean_box(0);
v___x_24_ = lean_apply_1(v_h__2_19_, v___x_23_);
return v___x_24_;
}
default: 
{
lean_object* v___x_25_; lean_object* v___x_26_; 
lean_dec(v_h__2_19_);
lean_dec(v_h__1_18_);
v___x_25_ = lean_box(v_x_17_);
v___x_26_ = lean_apply_3(v_h__3_20_, v___x_25_, lean_box(0), lean_box(0));
return v___x_26_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_17_ = stack[0].m_num;
lean_object* v_h__1_18_ = stack[1].m_obj;
lean_object* v_h__2_19_ = stack[2].m_obj;
lean_object* v_h__3_20_ = stack[3].m_obj;
lean_object* v_res_27_;
v_res_27_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter___redArg(v_x_17_, v_h__1_18_, v_h__2_19_, v_h__3_20_);
stack->m_obj
 = v_res_27_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter___redArg___boxed(lean_object* v_x_28_, lean_object* v_h__1_29_, lean_object* v_h__2_30_, lean_object* v_h__3_31_){
_start:
{
uint8_t v_x_18__boxed_32_; lean_object* v_res_33_; 
v_x_18__boxed_32_ = lean_unbox(v_x_28_);
v_res_33_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter___redArg(v_x_18__boxed_32_, v_h__1_29_, v_h__2_30_, v_h__3_31_);
return v_res_33_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter(lean_object* v_motive_34_, uint8_t v_x_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_, lean_object* v_h__3_38_){
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
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_35_ = stack[1].m_num;
lean_object* v_h__1_36_ = stack[2].m_obj;
lean_object* v_h__2_37_ = stack[3].m_obj;
lean_object* v_h__3_38_ = stack[4].m_obj;
lean_object* v_res_45_;
v_res_45_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter(lean_box(0), v_x_35_, v_h__1_36_, v_h__2_37_, v_h__3_38_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter___boxed(lean_object* v_motive_46_, lean_object* v_x_47_, lean_object* v_h__1_48_, lean_object* v_h__2_49_, lean_object* v_h__3_50_){
_start:
{
uint8_t v_x_41__boxed_51_; lean_object* v_res_52_; 
v_x_41__boxed_51_ = lean_unbox(v_x_47_);
v_res_52_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter(v_motive_46_, v_x_41__boxed_51_, v_h__1_48_, v_h__2_49_, v_h__3_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_go(lean_object* v_argKinds_53_, lean_object* v_i_54_){
_start:
{
lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_55_ = lean_array_get_size(v_argKinds_53_);
v___x_56_ = lean_nat_dec_lt(v_i_54_, v___x_55_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; 
lean_dec(v_i_54_);
v___x_57_ = lean_box(0);
return v___x_57_;
}
else
{
lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_58_ = lean_array_fget_borrowed(v_argKinds_53_, v_i_54_);
v___x_59_ = lean_unbox(v___x_58_);
switch(v___x_59_)
{
case 0:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(1u);
v___x_61_ = lean_nat_add(v_i_54_, v___x_60_);
lean_dec(v_i_54_);
v_i_54_ = v___x_61_;
goto _start;
}
case 2:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_unsigned_to_nat(1u);
v___x_64_ = lean_nat_add(v_i_54_, v___x_63_);
v___x_65_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq(v_argKinds_53_, v_i_54_, v___x_64_);
return v___x_65_;
}
default: 
{
lean_object* v___x_66_; 
lean_dec(v_i_54_);
v___x_66_ = lean_box(0);
return v___x_66_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_go___boxed(lean_object* v_argKinds_67_, lean_object* v_i_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_go(v_argKinds_67_, v_i_68_);
lean_dec_ref(v_argKinds_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f(lean_object* v_argKinds_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(0u);
v___x_72_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_go(v_argKinds_70_, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f___boxed(lean_object* v_argKinds_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f(v_argKinds_73_);
lean_dec_ref(v_argKinds_73_);
return v_res_74_;
}
}
uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg(lean_object* v_xs_75_, lean_object* v_ys_76_, lean_object* v_x_77_){
_start:
{
lean_object* v_zero_78_; uint8_t v_isZero_79_; 
v_zero_78_ = lean_unsigned_to_nat(0u);
v_isZero_79_ = lean_nat_dec_eq(v_x_77_, v_zero_78_);
if (v_isZero_79_ == 1)
{
lean_dec(v_x_77_);
return v_isZero_79_;
}
else
{
lean_object* v_one_80_; lean_object* v_n_81_; lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; uint8_t v___x_85_; uint8_t v___x_86_; 
v_one_80_ = lean_unsigned_to_nat(1u);
v_n_81_ = lean_nat_sub(v_x_77_, v_one_80_);
lean_dec(v_x_77_);
v___x_82_ = lean_array_fget_borrowed(v_xs_75_, v_n_81_);
v___x_83_ = lean_array_fget_borrowed(v_ys_76_, v_n_81_);
v___x_84_ = lean_unbox(v___x_82_);
v___x_85_ = lean_unbox(v___x_83_);
v___x_86_ = l_Lean_Meta_instBEqCongrArgKind_beq(v___x_84_, v___x_85_);
if (v___x_86_ == 0)
{
lean_dec(v_n_81_);
return v___x_86_;
}
else
{
v_x_77_ = v_n_81_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_75_ = stack[0].m_obj;
lean_object* v_ys_76_ = stack[1].m_obj;
lean_object* v_x_77_ = stack[2].m_obj;
uint8_t v_res_88_;
v_res_88_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg(v_xs_75_, v_ys_76_, v_x_77_);
stack->m_num = v_res_88_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg___boxed(lean_object* v_xs_89_, lean_object* v_ys_90_, lean_object* v_x_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg(v_xs_89_, v_ys_90_, v_x_91_);
lean_dec_ref(v_ys_90_);
lean_dec_ref(v_xs_89_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0(uint8_t v___y_94_, uint8_t v_a_95_, lean_object* v_as_96_, size_t v_i_97_, size_t v_stop_98_){
_start:
{
uint8_t v___x_99_; 
v___x_99_ = lean_usize_dec_eq(v_i_97_, v_stop_98_);
if (v___x_99_ == 0)
{
uint8_t v___x_100_; uint8_t v___y_102_; lean_object* v___x_106_; uint8_t v___x_107_; uint8_t v___x_108_; uint8_t v___x_109_; 
v___x_100_ = 1;
v___x_106_ = lean_array_uget_borrowed(v_as_96_, v_i_97_);
v___x_107_ = 0;
v___x_108_ = lean_unbox(v___x_106_);
v___x_109_ = l_Lean_Meta_instBEqCongrArgKind_beq(v___x_108_, v___x_107_);
if (v___x_109_ == 0)
{
v___y_102_ = v___y_94_;
goto v___jp_101_;
}
else
{
v___y_102_ = v_a_95_;
goto v___jp_101_;
}
v___jp_101_:
{
if (v___y_102_ == 0)
{
size_t v___x_103_; size_t v___x_104_; 
v___x_103_ = ((size_t)1ULL);
v___x_104_ = lean_usize_add(v_i_97_, v___x_103_);
v_i_97_ = v___x_104_;
goto _start;
}
else
{
return v___x_100_;
}
}
}
else
{
uint8_t v___x_110_; 
v___x_110_ = 0;
return v___x_110_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_94_ = stack[0].m_num;
uint8_t v_a_95_ = stack[1].m_num;
lean_object* v_as_96_ = stack[2].m_obj;
size_t v_i_97_ = stack[3].m_num;
size_t v_stop_98_ = stack[4].m_num;
uint8_t v_res_111_;
v_res_111_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0(v___y_94_, v_a_95_, v_as_96_, v_i_97_, v_stop_98_);
stack->m_num = v_res_111_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0___boxed(lean_object* v___y_112_, lean_object* v_a_113_, lean_object* v_as_114_, lean_object* v_i_115_, lean_object* v_stop_116_){
_start:
{
uint8_t v___y_6092__boxed_117_; uint8_t v_a_6093__boxed_118_; size_t v_i_boxed_119_; size_t v_stop_boxed_120_; uint8_t v_res_121_; lean_object* v_r_122_; 
v___y_6092__boxed_117_ = lean_unbox(v___y_112_);
v_a_6093__boxed_118_ = lean_unbox(v_a_113_);
v_i_boxed_119_ = lean_unbox_usize(v_i_115_);
lean_dec(v_i_115_);
v_stop_boxed_120_ = lean_unbox_usize(v_stop_116_);
lean_dec(v_stop_116_);
v_res_121_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0(v___y_6092__boxed_117_, v_a_6093__boxed_118_, v_as_114_, v_i_boxed_119_, v_stop_boxed_120_);
lean_dec_ref(v_as_114_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1(size_t v_sz_123_, size_t v_i_124_, lean_object* v_bs_125_){
_start:
{
uint8_t v___x_126_; 
v___x_126_ = lean_usize_dec_lt(v_i_124_, v_sz_123_);
if (v___x_126_ == 0)
{
return v_bs_125_;
}
else
{
lean_object* v_v_127_; lean_object* v___x_128_; lean_object* v_bs_x27_129_; uint8_t v___x_130_; uint8_t v___x_131_; uint8_t v___x_132_; size_t v___x_133_; size_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_v_127_ = lean_array_uget(v_bs_125_, v_i_124_);
v___x_128_ = lean_unsigned_to_nat(0u);
v_bs_x27_129_ = lean_array_uset(v_bs_125_, v_i_124_, v___x_128_);
v___x_130_ = 2;
v___x_131_ = lean_unbox(v_v_127_);
lean_dec(v_v_127_);
v___x_132_ = l_Lean_Meta_instBEqCongrArgKind_beq(v___x_131_, v___x_130_);
v___x_133_ = ((size_t)1ULL);
v___x_134_ = lean_usize_add(v_i_124_, v___x_133_);
v___x_135_ = lean_box(v___x_132_);
v___x_136_ = lean_array_uset(v_bs_x27_129_, v_i_124_, v___x_135_);
v_i_124_ = v___x_134_;
v_bs_125_ = v___x_136_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_123_ = stack[0].m_num;
size_t v_i_124_ = stack[1].m_num;
lean_object* v_bs_125_ = stack[2].m_obj;
lean_object* v_res_138_;
v_res_138_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1(v_sz_123_, v_i_124_, v_bs_125_);
stack->m_obj
 = v_res_138_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1___boxed(lean_object* v_sz_139_, lean_object* v_i_140_, lean_object* v_bs_141_){
_start:
{
size_t v_sz_boxed_142_; size_t v_i_boxed_143_; lean_object* v_res_144_; 
v_sz_boxed_142_ = lean_unbox_usize(v_sz_139_);
lean_dec(v_sz_139_);
v_i_boxed_143_ = lean_unbox_usize(v_i_140_);
lean_dec(v_i_140_);
v_res_144_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1(v_sz_boxed_142_, v_i_boxed_143_, v_bs_141_);
return v_res_144_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2(uint8_t v_a_145_, lean_object* v_as_146_, size_t v_i_147_, size_t v_stop_148_){
_start:
{
uint8_t v___x_149_; 
v___x_149_ = lean_usize_dec_eq(v_i_147_, v_stop_148_);
if (v___x_149_ == 0)
{
uint8_t v___x_150_; uint8_t v___y_152_; lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_150_ = 1;
v___x_156_ = lean_array_uget_borrowed(v_as_146_, v_i_147_);
v___x_157_ = lean_unbox(v___x_156_);
switch(v___x_157_)
{
case 0:
{
v___y_152_ = v_a_145_;
goto v___jp_151_;
}
case 2:
{
v___y_152_ = v_a_145_;
goto v___jp_151_;
}
default: 
{
return v___x_150_;
}
}
v___jp_151_:
{
if (v___y_152_ == 0)
{
size_t v___x_153_; size_t v___x_154_; 
v___x_153_ = ((size_t)1ULL);
v___x_154_ = lean_usize_add(v_i_147_, v___x_153_);
v_i_147_ = v___x_154_;
goto _start;
}
else
{
return v___x_150_;
}
}
}
else
{
uint8_t v___x_158_; 
v___x_158_ = 0;
return v___x_158_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_145_ = stack[0].m_num;
lean_object* v_as_146_ = stack[1].m_obj;
size_t v_i_147_ = stack[2].m_num;
size_t v_stop_148_ = stack[3].m_num;
uint8_t v_res_159_;
v_res_159_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2(v_a_145_, v_as_146_, v_i_147_, v_stop_148_);
stack->m_num = v_res_159_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2___boxed(lean_object* v_a_160_, lean_object* v_as_161_, lean_object* v_i_162_, lean_object* v_stop_163_){
_start:
{
uint8_t v_a_6168__boxed_164_; size_t v_i_boxed_165_; size_t v_stop_boxed_166_; uint8_t v_res_167_; lean_object* v_r_168_; 
v_a_6168__boxed_164_ = lean_unbox(v_a_160_);
v_i_boxed_165_ = lean_unbox_usize(v_i_162_);
lean_dec(v_i_162_);
v_stop_boxed_166_ = lean_unbox_usize(v_stop_163_);
lean_dec(v_stop_163_);
v_res_167_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2(v_a_6168__boxed_164_, v_as_161_, v_i_boxed_165_, v_stop_boxed_166_);
lean_dec_ref(v_as_161_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(lean_object* v_f_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_){
_start:
{
lean_object* v___x_175_; 
lean_inc_ref(v_f_169_);
v___x_175_ = l_Lean_Meta_isProof(v_f_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_312_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_312_ == 0)
{
v___x_178_ = v___x_175_;
v_isShared_179_ = v_isSharedCheck_312_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_175_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_312_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
uint8_t v___x_180_; 
v___x_180_ = lean_unbox(v_a_176_);
if (v___x_180_ == 0)
{
uint8_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
lean_del_object(v___x_178_);
v___x_181_ = 1;
v___x_182_ = lean_box(0);
lean_inc_ref(v_f_169_);
v___x_183_ = l_Lean_Meta_getFunInfo(v_f_169_, v___x_182_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_299_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_299_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_299_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_299_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; 
lean_inc_ref(v_f_169_);
v___x_188_ = l_Lean_Meta_getCongrSimpKinds(v_f_169_, v_a_184_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_290_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_290_ == 0)
{
v___x_191_ = v___x_188_;
v_isShared_192_ = v_isSharedCheck_290_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_290_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___y_199_; lean_object* v___y_200_; lean_object* v___y_201_; lean_object* v___y_202_; lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___y_235_; uint8_t v___x_254_; 
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = lean_array_get_size(v_a_189_);
v___x_254_ = lean_nat_dec_lt(v___x_232_, v___x_233_);
if (v___x_254_ == 0)
{
lean_dec(v_a_184_);
lean_dec_ref(v_f_169_);
v___y_235_ = v___x_181_;
goto v___jp_234_;
}
else
{
if (v___x_254_ == 0)
{
lean_dec(v_a_184_);
lean_dec_ref(v_f_169_);
v___y_235_ = v___x_181_;
goto v___jp_234_;
}
else
{
size_t v___x_255_; size_t v___x_256_; uint8_t v___x_257_; uint8_t v___x_258_; 
v___x_255_ = ((size_t)0ULL);
v___x_256_ = lean_usize_of_nat(v___x_233_);
v___x_257_ = lean_unbox(v_a_176_);
v___x_258_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2(v___x_257_, v_a_189_, v___x_255_, v___x_256_);
if (v___x_258_ == 0)
{
lean_dec(v_a_184_);
lean_dec_ref(v_f_169_);
v___y_235_ = v___x_254_;
goto v___jp_234_;
}
else
{
lean_del_object(v___x_191_);
lean_del_object(v___x_186_);
lean_dec(v_a_176_);
if (lean_obj_tag(v_f_169_) == 4)
{
lean_object* v_declName_259_; lean_object* v_us_260_; lean_object* v___x_261_; 
v_declName_259_ = lean_ctor_get(v_f_169_, 0);
v_us_260_ = lean_ctor_get(v_f_169_, 1);
lean_inc(v_us_260_);
lean_inc(v_declName_259_);
v___x_261_ = l_Lean_Meta_mkCongrSimpForConst_x3f(v_declName_259_, v_us_260_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_281_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_281_ == 0)
{
v___x_264_ = v___x_261_;
v_isShared_265_ = v_isSharedCheck_281_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_261_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_281_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
if (lean_obj_tag(v_a_262_) == 1)
{
lean_object* v_val_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_280_; 
v_val_266_ = lean_ctor_get(v_a_262_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v_a_262_);
if (v_isSharedCheck_280_ == 0)
{
v___x_268_ = v_a_262_;
v_isShared_269_ = v_isSharedCheck_280_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_val_266_);
lean_dec(v_a_262_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_280_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v_argKinds_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_argKinds_270_ = lean_ctor_get(v_val_266_, 2);
v___x_271_ = lean_array_get_size(v_argKinds_270_);
v___x_272_ = lean_nat_dec_eq(v___x_271_, v___x_233_);
if (v___x_272_ == 0)
{
lean_del_object(v___x_268_);
lean_dec(v_val_266_);
lean_del_object(v___x_264_);
v___y_199_ = v_a_170_;
v___y_200_ = v_a_171_;
v___y_201_ = v_a_172_;
v___y_202_ = v_a_173_;
goto v___jp_198_;
}
else
{
uint8_t v___x_273_; 
v___x_273_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg(v_argKinds_270_, v_a_189_, v___x_271_);
if (v___x_273_ == 0)
{
lean_del_object(v___x_268_);
lean_dec(v_val_266_);
lean_del_object(v___x_264_);
v___y_199_ = v_a_170_;
v___y_200_ = v_a_171_;
v___y_201_ = v_a_172_;
v___y_202_ = v_a_173_;
goto v___jp_198_;
}
else
{
lean_object* v___x_275_; 
lean_dec_ref_known(v_f_169_, 2);
lean_dec(v_a_189_);
lean_dec(v_a_184_);
if (v_isShared_269_ == 0)
{
lean_ctor_set_tag(v___x_268_, 3);
v___x_275_ = v___x_268_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_val_266_);
v___x_275_ = v_reuseFailAlloc_279_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_277_; 
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 0, v___x_275_);
v___x_277_ = v___x_264_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_264_);
lean_dec(v_a_262_);
v___y_199_ = v_a_170_;
v___y_200_ = v_a_171_;
v___y_201_ = v_a_172_;
v___y_202_ = v_a_173_;
goto v___jp_198_;
}
}
}
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
lean_dec_ref_known(v_f_169_, 2);
lean_dec(v_a_189_);
lean_dec(v_a_184_);
v_a_282_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_261_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_261_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
else
{
v___y_199_ = v_a_170_;
v___y_200_ = v_a_171_;
v___y_201_ = v_a_172_;
v___y_202_ = v_a_173_;
goto v___jp_198_;
}
}
}
}
v___jp_193_:
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = lean_box(0);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_194_);
v___x_196_ = v___x_191_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
v___jp_198_:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Meta_mkCongrSimpCore_x3f(v_f_169_, v_a_184_, v_a_189_, v___x_181_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_223_; 
v_a_204_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_223_ == 0)
{
v___x_206_ = v___x_203_;
v_isShared_207_ = v_isSharedCheck_223_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_203_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_223_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
if (lean_obj_tag(v_a_204_) == 1)
{
lean_object* v_val_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_218_; 
v_val_208_ = lean_ctor_get(v_a_204_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v_a_204_);
if (v_isSharedCheck_218_ == 0)
{
v___x_210_ = v_a_204_;
v_isShared_211_ = v_isSharedCheck_218_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_val_208_);
lean_dec(v_a_204_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_218_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
lean_ctor_set_tag(v___x_210_, 3);
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_val_208_);
v___x_213_ = v_reuseFailAlloc_217_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_215_; 
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 0, v___x_213_);
v___x_215_ = v___x_206_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
else
{
lean_object* v___x_219_; lean_object* v___x_221_; 
lean_dec(v_a_204_);
v___x_219_ = lean_box(0);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 0, v___x_219_);
v___x_221_ = v___x_206_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
else
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
v_a_224_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v___x_203_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_203_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
v___jp_234_:
{
uint8_t v___x_236_; 
v___x_236_ = lean_nat_dec_lt(v___x_232_, v___x_233_);
if (v___x_236_ == 0)
{
lean_dec(v_a_189_);
lean_del_object(v___x_186_);
lean_dec(v_a_176_);
goto v___jp_193_;
}
else
{
if (v___x_236_ == 0)
{
lean_dec(v_a_189_);
lean_del_object(v___x_186_);
lean_dec(v_a_176_);
goto v___jp_193_;
}
else
{
size_t v___x_237_; size_t v___x_238_; uint8_t v___x_239_; uint8_t v___x_240_; 
v___x_237_ = ((size_t)0ULL);
v___x_238_ = lean_usize_of_nat(v___x_233_);
v___x_239_ = lean_unbox(v_a_176_);
lean_dec(v_a_176_);
v___x_240_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0(v___y_235_, v___x_239_, v_a_189_, v___x_237_, v___x_238_);
if (v___x_240_ == 0)
{
lean_dec(v_a_189_);
lean_del_object(v___x_186_);
goto v___jp_193_;
}
else
{
lean_object* v___x_241_; 
lean_del_object(v___x_191_);
v___x_241_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f(v_a_189_);
if (lean_obj_tag(v___x_241_) == 1)
{
lean_object* v_val_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
lean_dec(v_a_189_);
v_val_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_val_242_);
lean_dec_ref_known(v___x_241_, 1);
v___x_243_ = lean_nat_sub(v___x_233_, v_val_242_);
v___x_244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_244_, 0, v_val_242_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_244_);
v___x_246_ = v___x_186_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
else
{
size_t v_sz_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_252_; 
lean_dec(v___x_241_);
v_sz_248_ = lean_array_size(v_a_189_);
v___x_249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1(v_sz_248_, v___x_237_, v_a_189_);
v___x_250_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_250_);
v___x_252_ = v___x_186_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_del_object(v___x_186_);
lean_dec(v_a_184_);
lean_dec(v_a_176_);
lean_dec_ref(v_f_169_);
v_a_291_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_188_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_188_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec(v_a_176_);
lean_dec_ref(v_f_169_);
v_a_300_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_183_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_183_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
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
lean_object* v___x_308_; lean_object* v___x_310_; 
lean_dec(v_a_176_);
lean_dec_ref(v_f_169_);
v___x_308_ = lean_box(0);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_308_);
v___x_310_ = v___x_178_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_dec_ref(v_f_169_);
v_a_313_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_175_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_175_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_169_ = stack[0].m_obj;
lean_object* v_a_170_ = stack[1].m_obj;
lean_object* v_a_171_ = stack[2].m_obj;
lean_object* v_a_172_ = stack[3].m_obj;
lean_object* v_a_173_ = stack[4].m_obj;
lean_object* v_res_321_;
v_res_321_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(v_f_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
stack->m_obj
 = v_res_321_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg___boxed(lean_object* v_f_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(v_f_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
return v_res_328_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo(lean_object* v_f_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(v_f_329_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
return v___x_337_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_329_ = stack[0].m_obj;
lean_object* v_a_330_ = stack[1].m_obj;
lean_object* v_a_331_ = stack[2].m_obj;
lean_object* v_a_332_ = stack[3].m_obj;
lean_object* v_a_333_ = stack[4].m_obj;
lean_object* v_a_334_ = stack[5].m_obj;
lean_object* v_a_335_ = stack[6].m_obj;
lean_object* v_res_338_;
v_res_338_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo(v_f_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
stack->m_obj
 = v_res_338_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___boxed(lean_object* v_f_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo(v_f_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
return v_res_347_;
}
}
uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3(lean_object* v_xs_348_, lean_object* v_ys_349_, lean_object* v_hsz_350_, lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
uint8_t v___x_353_; 
v___x_353_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg(v_xs_348_, v_ys_349_, v_x_351_);
return v___x_353_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_348_ = stack[0].m_obj;
lean_object* v_ys_349_ = stack[1].m_obj;
lean_object* v_x_351_ = stack[3].m_obj;
uint8_t v_res_354_;
v_res_354_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3(v_xs_348_, v_ys_349_, lean_box(0), v_x_351_, lean_box(0));
stack->m_num = v_res_354_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___boxed(lean_object* v_xs_355_, lean_object* v_ys_356_, lean_object* v_hsz_357_, lean_object* v_x_358_, lean_object* v_x_359_){
_start:
{
uint8_t v_res_360_; lean_object* v_r_361_; 
v_res_360_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3(v_xs_355_, v_ys_356_, v_hsz_357_, v_x_358_, v_x_359_);
lean_dec_ref(v_ys_356_);
lean_dec_ref(v_xs_355_);
v_r_361_ = lean_box(v_res_360_);
return v_r_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_362_, lean_object* v_x_363_, lean_object* v_x_364_, lean_object* v_x_365_){
_start:
{
lean_object* v_ks_366_; lean_object* v_vs_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_393_; 
v_ks_366_ = lean_ctor_get(v_x_362_, 0);
v_vs_367_ = lean_ctor_get(v_x_362_, 1);
v_isSharedCheck_393_ = !lean_is_exclusive(v_x_362_);
if (v_isSharedCheck_393_ == 0)
{
v___x_369_ = v_x_362_;
v_isShared_370_ = v_isSharedCheck_393_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_vs_367_);
lean_inc(v_ks_366_);
lean_dec(v_x_362_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_393_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = lean_array_get_size(v_ks_366_);
v___x_372_ = lean_nat_dec_lt(v_x_363_, v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
lean_dec(v_x_363_);
v___x_373_ = lean_array_push(v_ks_366_, v_x_364_);
v___x_374_ = lean_array_push(v_vs_367_, v_x_365_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v___x_374_);
lean_ctor_set(v___x_369_, 0, v___x_373_);
v___x_376_ = v___x_369_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_373_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
else
{
lean_object* v_k_x27_378_; size_t v___x_379_; size_t v___x_380_; uint8_t v___x_381_; 
v_k_x27_378_ = lean_array_fget_borrowed(v_ks_366_, v_x_363_);
v___x_379_ = lean_ptr_addr(v_x_364_);
v___x_380_ = lean_ptr_addr(v_k_x27_378_);
v___x_381_ = lean_usize_dec_eq(v___x_379_, v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_383_; 
if (v_isShared_370_ == 0)
{
v___x_383_ = v___x_369_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_ks_366_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_vs_367_);
v___x_383_ = v_reuseFailAlloc_387_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_unsigned_to_nat(1u);
v___x_385_ = lean_nat_add(v_x_363_, v___x_384_);
lean_dec(v_x_363_);
v_x_362_ = v___x_383_;
v_x_363_ = v___x_385_;
goto _start;
}
}
else
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_388_ = lean_array_fset(v_ks_366_, v_x_363_, v_x_364_);
v___x_389_ = lean_array_fset(v_vs_367_, v_x_363_, v_x_365_);
lean_dec(v_x_363_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v___x_389_);
lean_ctor_set(v___x_369_, 0, v___x_388_);
v___x_391_ = v___x_369_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v___x_389_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4___redArg(lean_object* v_n_394_, lean_object* v_k_395_, lean_object* v_v_396_){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5___redArg(v_n_394_, v___x_397_, v_k_395_, v_v_396_);
return v___x_398_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_399_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(lean_object* v_x_400_, size_t v_x_401_, size_t v_x_402_, lean_object* v_x_403_, lean_object* v_x_404_){
_start:
{
if (lean_obj_tag(v_x_400_) == 0)
{
lean_object* v_es_405_; size_t v___x_406_; size_t v___x_407_; lean_object* v_j_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v_es_405_ = lean_ctor_get(v_x_400_, 0);
v___x_406_ = ((size_t)31ULL);
v___x_407_ = lean_usize_land(v_x_401_, v___x_406_);
v_j_408_ = lean_usize_to_nat(v___x_407_);
v___x_409_ = lean_array_get_size(v_es_405_);
v___x_410_ = lean_nat_dec_lt(v_j_408_, v___x_409_);
if (v___x_410_ == 0)
{
lean_dec(v_j_408_);
lean_dec(v_x_404_);
lean_dec_ref(v_x_403_);
return v_x_400_;
}
else
{
lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_451_; 
lean_inc_ref(v_es_405_);
v_isSharedCheck_451_ = !lean_is_exclusive(v_x_400_);
if (v_isSharedCheck_451_ == 0)
{
lean_object* v_unused_452_; 
v_unused_452_ = lean_ctor_get(v_x_400_, 0);
lean_dec(v_unused_452_);
v___x_412_ = v_x_400_;
v_isShared_413_ = v_isSharedCheck_451_;
goto v_resetjp_411_;
}
else
{
lean_dec(v_x_400_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_451_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v_v_414_; lean_object* v___x_415_; lean_object* v_xs_x27_416_; lean_object* v___y_418_; 
v_v_414_ = lean_array_fget(v_es_405_, v_j_408_);
v___x_415_ = lean_box(0);
v_xs_x27_416_ = lean_array_fset(v_es_405_, v_j_408_, v___x_415_);
switch(lean_obj_tag(v_v_414_))
{
case 0:
{
lean_object* v_key_423_; lean_object* v_val_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_436_; 
v_key_423_ = lean_ctor_get(v_v_414_, 0);
v_val_424_ = lean_ctor_get(v_v_414_, 1);
v_isSharedCheck_436_ = !lean_is_exclusive(v_v_414_);
if (v_isSharedCheck_436_ == 0)
{
v___x_426_ = v_v_414_;
v_isShared_427_ = v_isSharedCheck_436_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_val_424_);
lean_inc(v_key_423_);
lean_dec(v_v_414_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_436_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
size_t v___x_428_; size_t v___x_429_; uint8_t v___x_430_; 
v___x_428_ = lean_ptr_addr(v_x_403_);
v___x_429_ = lean_ptr_addr(v_key_423_);
v___x_430_ = lean_usize_dec_eq(v___x_428_, v___x_429_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; lean_object* v___x_432_; 
lean_del_object(v___x_426_);
v___x_431_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_423_, v_val_424_, v_x_403_, v_x_404_);
v___x_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
v___y_418_ = v___x_432_;
goto v___jp_417_;
}
else
{
lean_object* v___x_434_; 
lean_dec(v_val_424_);
lean_dec(v_key_423_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v_x_404_);
lean_ctor_set(v___x_426_, 0, v_x_403_);
v___x_434_ = v___x_426_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_x_403_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_x_404_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
v___y_418_ = v___x_434_;
goto v___jp_417_;
}
}
}
}
case 1:
{
lean_object* v_node_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_449_; 
v_node_437_ = lean_ctor_get(v_v_414_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v_v_414_);
if (v_isSharedCheck_449_ == 0)
{
v___x_439_ = v_v_414_;
v_isShared_440_ = v_isSharedCheck_449_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_node_437_);
lean_dec(v_v_414_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_449_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
size_t v___x_441_; size_t v___x_442_; size_t v___x_443_; size_t v___x_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_441_ = ((size_t)5ULL);
v___x_442_ = lean_usize_shift_right(v_x_401_, v___x_441_);
v___x_443_ = ((size_t)1ULL);
v___x_444_ = lean_usize_add(v_x_402_, v___x_443_);
v___x_445_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_node_437_, v___x_442_, v___x_444_, v_x_403_, v_x_404_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_445_);
v___x_447_ = v___x_439_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
v___y_418_ = v___x_447_;
goto v___jp_417_;
}
}
}
default: 
{
lean_object* v___x_450_; 
v___x_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_450_, 0, v_x_403_);
lean_ctor_set(v___x_450_, 1, v_x_404_);
v___y_418_ = v___x_450_;
goto v___jp_417_;
}
}
v___jp_417_:
{
lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_419_ = lean_array_fset(v_xs_x27_416_, v_j_408_, v___y_418_);
lean_dec(v_j_408_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_419_);
v___x_421_ = v___x_412_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
else
{
lean_object* v_ks_453_; lean_object* v_vs_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_472_; 
v_ks_453_ = lean_ctor_get(v_x_400_, 0);
v_vs_454_ = lean_ctor_get(v_x_400_, 1);
v_isSharedCheck_472_ = !lean_is_exclusive(v_x_400_);
if (v_isSharedCheck_472_ == 0)
{
v___x_456_ = v_x_400_;
v_isShared_457_ = v_isSharedCheck_472_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_vs_454_);
lean_inc(v_ks_453_);
lean_dec(v_x_400_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_472_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_ks_453_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_vs_454_);
v___x_459_ = v_reuseFailAlloc_471_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v_newNode_460_; size_t v___x_461_; uint8_t v___x_462_; 
v_newNode_460_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4___redArg(v___x_459_, v_x_403_, v_x_404_);
v___x_461_ = ((size_t)7ULL);
v___x_462_ = lean_usize_dec_le(v___x_461_, v_x_402_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_463_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_460_);
v___x_464_ = lean_unsigned_to_nat(4u);
v___x_465_ = lean_nat_dec_lt(v___x_463_, v___x_464_);
lean_dec(v___x_463_);
if (v___x_465_ == 0)
{
lean_object* v_ks_466_; lean_object* v_vs_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v_ks_466_ = lean_ctor_get(v_newNode_460_, 0);
lean_inc_ref(v_ks_466_);
v_vs_467_ = lean_ctor_get(v_newNode_460_, 1);
lean_inc_ref(v_vs_467_);
lean_dec_ref(v_newNode_460_);
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0);
v___x_470_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(v_x_402_, v_ks_466_, v_vs_467_, v___x_468_, v___x_469_);
lean_dec_ref(v_vs_467_);
lean_dec_ref(v_ks_466_);
return v___x_470_;
}
else
{
return v_newNode_460_;
}
}
else
{
return v_newNode_460_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_400_ = stack[0].m_obj;
size_t v_x_401_ = stack[1].m_num;
size_t v_x_402_ = stack[2].m_num;
lean_object* v_x_403_ = stack[3].m_obj;
lean_object* v_x_404_ = stack[4].m_obj;
lean_object* v_res_473_;
v_res_473_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_x_400_, v_x_401_, v_x_402_, v_x_403_, v_x_404_);
stack->m_obj
 = v_res_473_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(size_t v_depth_474_, lean_object* v_keys_475_, lean_object* v_vals_476_, lean_object* v_i_477_, lean_object* v_entries_478_){
_start:
{
lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = lean_array_get_size(v_keys_475_);
v___x_480_ = lean_nat_dec_lt(v_i_477_, v___x_479_);
if (v___x_480_ == 0)
{
lean_dec(v_i_477_);
return v_entries_478_;
}
else
{
lean_object* v_k_481_; lean_object* v_v_482_; size_t v___x_483_; size_t v___x_484_; size_t v___x_485_; uint64_t v___x_486_; size_t v_h_487_; size_t v___x_488_; lean_object* v___x_489_; size_t v___x_490_; size_t v___x_491_; size_t v___x_492_; size_t v_h_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_k_481_ = lean_array_fget_borrowed(v_keys_475_, v_i_477_);
v_v_482_ = lean_array_fget_borrowed(v_vals_476_, v_i_477_);
v___x_483_ = lean_ptr_addr(v_k_481_);
v___x_484_ = ((size_t)3ULL);
v___x_485_ = lean_usize_shift_right(v___x_483_, v___x_484_);
v___x_486_ = lean_usize_to_uint64(v___x_485_);
v_h_487_ = lean_uint64_to_usize(v___x_486_);
v___x_488_ = ((size_t)5ULL);
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = ((size_t)1ULL);
v___x_491_ = lean_usize_sub(v_depth_474_, v___x_490_);
v___x_492_ = lean_usize_mul(v___x_488_, v___x_491_);
v_h_493_ = lean_usize_shift_right(v_h_487_, v___x_492_);
v___x_494_ = lean_nat_add(v_i_477_, v___x_489_);
lean_dec(v_i_477_);
lean_inc(v_v_482_);
lean_inc(v_k_481_);
v___x_495_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_entries_478_, v_h_493_, v_depth_474_, v_k_481_, v_v_482_);
v_i_477_ = v___x_494_;
v_entries_478_ = v___x_495_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_474_ = stack[0].m_num;
lean_object* v_keys_475_ = stack[1].m_obj;
lean_object* v_vals_476_ = stack[2].m_obj;
lean_object* v_i_477_ = stack[3].m_obj;
lean_object* v_entries_478_ = stack[4].m_obj;
lean_object* v_res_497_;
v_res_497_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(v_depth_474_, v_keys_475_, v_vals_476_, v_i_477_, v_entries_478_);
stack->m_obj
 = v_res_497_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_498_, lean_object* v_keys_499_, lean_object* v_vals_500_, lean_object* v_i_501_, lean_object* v_entries_502_){
_start:
{
size_t v_depth_boxed_503_; lean_object* v_res_504_; 
v_depth_boxed_503_ = lean_unbox_usize(v_depth_498_);
lean_dec(v_depth_498_);
v_res_504_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(v_depth_boxed_503_, v_keys_499_, v_vals_500_, v_i_501_, v_entries_502_);
lean_dec_ref(v_vals_500_);
lean_dec_ref(v_keys_499_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___boxed(lean_object* v_x_505_, lean_object* v_x_506_, lean_object* v_x_507_, lean_object* v_x_508_, lean_object* v_x_509_){
_start:
{
size_t v_x_2578__boxed_510_; size_t v_x_2579__boxed_511_; lean_object* v_res_512_; 
v_x_2578__boxed_510_ = lean_unbox_usize(v_x_506_);
lean_dec(v_x_506_);
v_x_2579__boxed_511_ = lean_unbox_usize(v_x_507_);
lean_dec(v_x_507_);
v_res_512_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_x_505_, v_x_2578__boxed_510_, v_x_2579__boxed_511_, v_x_508_, v_x_509_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1___redArg(lean_object* v_x_513_, lean_object* v_x_514_, lean_object* v_x_515_){
_start:
{
size_t v___x_516_; size_t v___x_517_; size_t v___x_518_; uint64_t v___x_519_; size_t v___x_520_; size_t v___x_521_; lean_object* v___x_522_; 
v___x_516_ = lean_ptr_addr(v_x_514_);
v___x_517_ = ((size_t)3ULL);
v___x_518_ = lean_usize_shift_right(v___x_516_, v___x_517_);
v___x_519_ = lean_usize_to_uint64(v___x_518_);
v___x_520_ = lean_uint64_to_usize(v___x_519_);
v___x_521_ = ((size_t)1ULL);
v___x_522_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_x_513_, v___x_520_, v___x_521_, v_x_514_, v_x_515_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_523_, lean_object* v_vals_524_, lean_object* v_i_525_, lean_object* v_k_526_){
_start:
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = lean_array_get_size(v_keys_523_);
v___x_528_ = lean_nat_dec_lt(v_i_525_, v___x_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; 
lean_dec(v_i_525_);
v___x_529_ = lean_box(0);
return v___x_529_;
}
else
{
lean_object* v_k_x27_530_; size_t v___x_531_; size_t v___x_532_; uint8_t v___x_533_; 
v_k_x27_530_ = lean_array_fget_borrowed(v_keys_523_, v_i_525_);
v___x_531_ = lean_ptr_addr(v_k_526_);
v___x_532_ = lean_ptr_addr(v_k_x27_530_);
v___x_533_ = lean_usize_dec_eq(v___x_531_, v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = lean_nat_add(v_i_525_, v___x_534_);
lean_dec(v_i_525_);
v_i_525_ = v___x_535_;
goto _start;
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_array_fget_borrowed(v_vals_524_, v_i_525_);
lean_dec(v_i_525_);
lean_inc(v___x_537_);
v___x_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_539_, lean_object* v_vals_540_, lean_object* v_i_541_, lean_object* v_k_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(v_keys_539_, v_vals_540_, v_i_541_, v_k_542_);
lean_dec_ref(v_k_542_);
lean_dec_ref(v_vals_540_);
lean_dec_ref(v_keys_539_);
return v_res_543_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(lean_object* v_x_544_, size_t v_x_545_, lean_object* v_x_546_){
_start:
{
if (lean_obj_tag(v_x_544_) == 0)
{
lean_object* v_es_547_; lean_object* v___x_548_; size_t v___x_549_; size_t v___x_550_; lean_object* v_j_551_; lean_object* v___x_552_; 
v_es_547_ = lean_ctor_get(v_x_544_, 0);
v___x_548_ = lean_box(2);
v___x_549_ = ((size_t)31ULL);
v___x_550_ = lean_usize_land(v_x_545_, v___x_549_);
v_j_551_ = lean_usize_to_nat(v___x_550_);
v___x_552_ = lean_array_get_borrowed(v___x_548_, v_es_547_, v_j_551_);
lean_dec(v_j_551_);
switch(lean_obj_tag(v___x_552_))
{
case 0:
{
lean_object* v_key_553_; lean_object* v_val_554_; size_t v___x_555_; size_t v___x_556_; uint8_t v___x_557_; 
v_key_553_ = lean_ctor_get(v___x_552_, 0);
v_val_554_ = lean_ctor_get(v___x_552_, 1);
v___x_555_ = lean_ptr_addr(v_x_546_);
v___x_556_ = lean_ptr_addr(v_key_553_);
v___x_557_ = lean_usize_dec_eq(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
v___x_558_ = lean_box(0);
return v___x_558_;
}
else
{
lean_object* v___x_559_; 
lean_inc(v_val_554_);
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v_val_554_);
return v___x_559_;
}
}
case 1:
{
lean_object* v_node_560_; size_t v___x_561_; size_t v___x_562_; 
v_node_560_ = lean_ctor_get(v___x_552_, 0);
v___x_561_ = ((size_t)5ULL);
v___x_562_ = lean_usize_shift_right(v_x_545_, v___x_561_);
v_x_544_ = v_node_560_;
v_x_545_ = v___x_562_;
goto _start;
}
default: 
{
lean_object* v___x_564_; 
v___x_564_ = lean_box(0);
return v___x_564_;
}
}
}
else
{
lean_object* v_ks_565_; lean_object* v_vs_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_ks_565_ = lean_ctor_get(v_x_544_, 0);
v_vs_566_ = lean_ctor_get(v_x_544_, 1);
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(v_ks_565_, v_vs_566_, v___x_567_, v_x_546_);
return v___x_568_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_544_ = stack[0].m_obj;
size_t v_x_545_ = stack[1].m_num;
lean_object* v_x_546_ = stack[2].m_obj;
lean_object* v_res_569_;
v_res_569_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(v_x_544_, v_x_545_, v_x_546_);
stack->m_obj
 = v_res_569_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg___boxed(lean_object* v_x_570_, lean_object* v_x_571_, lean_object* v_x_572_){
_start:
{
size_t v_x_2889__boxed_573_; lean_object* v_res_574_; 
v_x_2889__boxed_573_ = lean_unbox_usize(v_x_571_);
lean_dec(v_x_571_);
v_res_574_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(v_x_570_, v_x_2889__boxed_573_, v_x_572_);
lean_dec_ref(v_x_572_);
lean_dec_ref(v_x_570_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(lean_object* v_x_575_, lean_object* v_x_576_){
_start:
{
size_t v___x_577_; size_t v___x_578_; size_t v___x_579_; uint64_t v___x_580_; size_t v___x_581_; lean_object* v___x_582_; 
v___x_577_ = lean_ptr_addr(v_x_576_);
v___x_578_ = ((size_t)3ULL);
v___x_579_ = lean_usize_shift_right(v___x_577_, v___x_578_);
v___x_580_ = lean_usize_to_uint64(v___x_579_);
v___x_581_ = lean_uint64_to_usize(v___x_580_);
v___x_582_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(v_x_575_, v___x_581_, v_x_576_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg___boxed(lean_object* v_x_583_, lean_object* v_x_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(v_x_583_, v_x_584_);
lean_dec_ref(v_x_584_);
lean_dec_ref(v_x_583_);
return v_res_585_;
}
}
lean_object* l_Lean_Meta_Sym_getCongrInfo___redArg(lean_object* v_f_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
lean_object* v___x_593_; lean_object* v_congrInfo_594_; lean_object* v___x_595_; 
v___x_593_ = lean_st_ref_get(v_a_587_);
v_congrInfo_594_ = lean_ctor_get(v___x_593_, 6);
lean_inc_ref(v_congrInfo_594_);
lean_dec(v___x_593_);
v___x_595_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(v_congrInfo_594_, v_f_586_);
lean_dec_ref(v_congrInfo_594_);
if (lean_obj_tag(v___x_595_) == 1)
{
lean_object* v_val_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec_ref(v_f_586_);
v_val_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_val_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set_tag(v___x_598_, 0);
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_val_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
else
{
lean_object* v___x_604_; 
lean_dec(v___x_595_);
lean_inc_ref(v_f_586_);
v___x_604_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(v_f_586_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_635_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_635_ == 0)
{
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_635_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_635_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v_share_610_; lean_object* v_maxFVar_611_; lean_object* v_proofInstInfo_612_; lean_object* v_proofInstInfoFVar_613_; lean_object* v_inferType_614_; lean_object* v_getLevel_615_; lean_object* v_congrInfo_616_; lean_object* v_defEqI_617_; lean_object* v_extensions_618_; lean_object* v_issues_619_; lean_object* v_canon_620_; lean_object* v_instanceOverrides_621_; uint8_t v_debug_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_634_; 
v___x_609_ = lean_st_ref_take(v_a_587_);
v_share_610_ = lean_ctor_get(v___x_609_, 0);
v_maxFVar_611_ = lean_ctor_get(v___x_609_, 1);
v_proofInstInfo_612_ = lean_ctor_get(v___x_609_, 2);
v_proofInstInfoFVar_613_ = lean_ctor_get(v___x_609_, 3);
v_inferType_614_ = lean_ctor_get(v___x_609_, 4);
v_getLevel_615_ = lean_ctor_get(v___x_609_, 5);
v_congrInfo_616_ = lean_ctor_get(v___x_609_, 6);
v_defEqI_617_ = lean_ctor_get(v___x_609_, 7);
v_extensions_618_ = lean_ctor_get(v___x_609_, 8);
v_issues_619_ = lean_ctor_get(v___x_609_, 9);
v_canon_620_ = lean_ctor_get(v___x_609_, 10);
v_instanceOverrides_621_ = lean_ctor_get(v___x_609_, 11);
v_debug_622_ = lean_ctor_get_uint8(v___x_609_, sizeof(void*)*12);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_634_ == 0)
{
v___x_624_ = v___x_609_;
v_isShared_625_ = v_isSharedCheck_634_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_instanceOverrides_621_);
lean_inc(v_canon_620_);
lean_inc(v_issues_619_);
lean_inc(v_extensions_618_);
lean_inc(v_defEqI_617_);
lean_inc(v_congrInfo_616_);
lean_inc(v_getLevel_615_);
lean_inc(v_inferType_614_);
lean_inc(v_proofInstInfoFVar_613_);
lean_inc(v_proofInstInfo_612_);
lean_inc(v_maxFVar_611_);
lean_inc(v_share_610_);
lean_dec(v___x_609_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_634_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_628_; 
lean_inc(v_a_605_);
v___x_626_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1___redArg(v_congrInfo_616_, v_f_586_, v_a_605_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 6, v___x_626_);
v___x_628_ = v___x_624_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_share_610_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_maxFVar_611_);
lean_ctor_set(v_reuseFailAlloc_633_, 2, v_proofInstInfo_612_);
lean_ctor_set(v_reuseFailAlloc_633_, 3, v_proofInstInfoFVar_613_);
lean_ctor_set(v_reuseFailAlloc_633_, 4, v_inferType_614_);
lean_ctor_set(v_reuseFailAlloc_633_, 5, v_getLevel_615_);
lean_ctor_set(v_reuseFailAlloc_633_, 6, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_633_, 7, v_defEqI_617_);
lean_ctor_set(v_reuseFailAlloc_633_, 8, v_extensions_618_);
lean_ctor_set(v_reuseFailAlloc_633_, 9, v_issues_619_);
lean_ctor_set(v_reuseFailAlloc_633_, 10, v_canon_620_);
lean_ctor_set(v_reuseFailAlloc_633_, 11, v_instanceOverrides_621_);
lean_ctor_set_uint8(v_reuseFailAlloc_633_, sizeof(void*)*12, v_debug_622_);
v___x_628_ = v_reuseFailAlloc_633_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_629_ = lean_st_ref_put(v_a_587_, v___x_628_);
if (v_isShared_608_ == 0)
{
v___x_631_ = v___x_607_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_605_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_586_);
return v___x_604_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getCongrInfo___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_586_ = stack[0].m_obj;
lean_object* v_a_587_ = stack[1].m_obj;
lean_object* v_a_588_ = stack[2].m_obj;
lean_object* v_a_589_ = stack[3].m_obj;
lean_object* v_a_590_ = stack[4].m_obj;
lean_object* v_a_591_ = stack[5].m_obj;
lean_object* v_res_636_;
v_res_636_ = l_Lean_Meta_Sym_getCongrInfo___redArg(v_f_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
stack->m_obj
 = v_res_636_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCongrInfo___redArg___boxed(lean_object* v_f_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_Meta_Sym_getCongrInfo___redArg(v_f_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
lean_dec(v_a_642_);
lean_dec_ref(v_a_641_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_a_638_);
return v_res_644_;
}
}
lean_object* l_Lean_Meta_Sym_getCongrInfo(lean_object* v_f_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_Meta_Sym_getCongrInfo___redArg(v_f_645_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_);
return v___x_653_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_getCongrInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_645_ = stack[0].m_obj;
lean_object* v_a_646_ = stack[1].m_obj;
lean_object* v_a_647_ = stack[2].m_obj;
lean_object* v_a_648_ = stack[3].m_obj;
lean_object* v_a_649_ = stack[4].m_obj;
lean_object* v_a_650_ = stack[5].m_obj;
lean_object* v_a_651_ = stack[6].m_obj;
lean_object* v_res_654_;
v_res_654_ = l_Lean_Meta_Sym_getCongrInfo(v_f_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_);
stack->m_obj
 = v_res_654_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCongrInfo___boxed(lean_object* v_f_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_Meta_Sym_getCongrInfo(v_f_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0(lean_object* v_00_u03b2_664_, lean_object* v_x_665_, lean_object* v_x_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(v_x_665_, v_x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___boxed(lean_object* v_00_u03b2_668_, lean_object* v_x_669_, lean_object* v_x_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0(v_00_u03b2_668_, v_x_669_, v_x_670_);
lean_dec_ref(v_x_670_);
lean_dec_ref(v_x_669_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1(lean_object* v_00_u03b2_672_, lean_object* v_x_673_, lean_object* v_x_674_, lean_object* v_x_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1___redArg(v_x_673_, v_x_674_, v_x_675_);
return v___x_676_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0(lean_object* v_00_u03b2_677_, lean_object* v_x_678_, size_t v_x_679_, lean_object* v_x_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(v_x_678_, v_x_679_, v_x_680_);
return v___x_681_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_678_ = stack[1].m_obj;
size_t v_x_679_ = stack[2].m_num;
lean_object* v_x_680_ = stack[3].m_obj;
lean_object* v_res_682_;
v_res_682_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0(lean_box(0), v_x_678_, v_x_679_, v_x_680_);
stack->m_obj
 = v_res_682_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___boxed(lean_object* v_00_u03b2_683_, lean_object* v_x_684_, lean_object* v_x_685_, lean_object* v_x_686_){
_start:
{
size_t v_x_3121__boxed_687_; lean_object* v_res_688_; 
v_x_3121__boxed_687_ = lean_unbox_usize(v_x_685_);
lean_dec(v_x_685_);
v_res_688_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0(v_00_u03b2_683_, v_x_684_, v_x_3121__boxed_687_, v_x_686_);
lean_dec_ref(v_x_686_);
lean_dec_ref(v_x_684_);
return v_res_688_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2(lean_object* v_00_u03b2_689_, lean_object* v_x_690_, size_t v_x_691_, size_t v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_x_690_, v_x_691_, v_x_692_, v_x_693_, v_x_694_);
return v___x_695_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_690_ = stack[1].m_obj;
size_t v_x_691_ = stack[2].m_num;
size_t v_x_692_ = stack[3].m_num;
lean_object* v_x_693_ = stack[4].m_obj;
lean_object* v_x_694_ = stack[5].m_obj;
lean_object* v_res_696_;
v_res_696_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2(lean_box(0), v_x_690_, v_x_691_, v_x_692_, v_x_693_, v_x_694_);
stack->m_obj
 = v_res_696_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___boxed(lean_object* v_00_u03b2_697_, lean_object* v_x_698_, lean_object* v_x_699_, lean_object* v_x_700_, lean_object* v_x_701_, lean_object* v_x_702_){
_start:
{
size_t v_x_3139__boxed_703_; size_t v_x_3140__boxed_704_; lean_object* v_res_705_; 
v_x_3139__boxed_703_ = lean_unbox_usize(v_x_699_);
lean_dec(v_x_699_);
v_x_3140__boxed_704_ = lean_unbox_usize(v_x_700_);
lean_dec(v_x_700_);
v_res_705_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2(v_00_u03b2_697_, v_x_698_, v_x_3139__boxed_703_, v_x_3140__boxed_704_, v_x_701_, v_x_702_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_706_, lean_object* v_keys_707_, lean_object* v_vals_708_, lean_object* v_heq_709_, lean_object* v_i_710_, lean_object* v_k_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(v_keys_707_, v_vals_708_, v_i_710_, v_k_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_713_, lean_object* v_keys_714_, lean_object* v_vals_715_, lean_object* v_heq_716_, lean_object* v_i_717_, lean_object* v_k_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1(v_00_u03b2_713_, v_keys_714_, v_vals_715_, v_heq_716_, v_i_717_, v_k_718_);
lean_dec_ref(v_k_718_);
lean_dec_ref(v_vals_715_);
lean_dec_ref(v_keys_714_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_720_, lean_object* v_n_721_, lean_object* v_k_722_, lean_object* v_v_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4___redArg(v_n_721_, v_k_722_, v_v_723_);
return v___x_724_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_725_, size_t v_depth_726_, lean_object* v_keys_727_, lean_object* v_vals_728_, lean_object* v_heq_729_, lean_object* v_i_730_, lean_object* v_entries_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(v_depth_726_, v_keys_727_, v_vals_728_, v_i_730_, v_entries_731_);
return v___x_732_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_depth_726_ = stack[1].m_num;
lean_object* v_keys_727_ = stack[2].m_obj;
lean_object* v_vals_728_ = stack[3].m_obj;
lean_object* v_i_730_ = stack[5].m_obj;
lean_object* v_entries_731_ = stack[6].m_obj;
lean_object* v_res_733_;
v_res_733_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5(lean_box(0), v_depth_726_, v_keys_727_, v_vals_728_, lean_box(0), v_i_730_, v_entries_731_);
stack->m_obj
 = v_res_733_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_734_, lean_object* v_depth_735_, lean_object* v_keys_736_, lean_object* v_vals_737_, lean_object* v_heq_738_, lean_object* v_i_739_, lean_object* v_entries_740_){
_start:
{
size_t v_depth_boxed_741_; lean_object* v_res_742_; 
v_depth_boxed_741_ = lean_unbox_usize(v_depth_735_);
lean_dec(v_depth_735_);
v_res_742_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5(v_00_u03b2_734_, v_depth_boxed_741_, v_keys_736_, v_vals_737_, v_heq_738_, v_i_739_, v_entries_740_);
lean_dec_ref(v_vals_737_);
lean_dec_ref(v_keys_736_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_743_, lean_object* v_x_744_, lean_object* v_x_745_, lean_object* v_x_746_, lean_object* v_x_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5___redArg(v_x_744_, v_x_745_, v_x_746_, v_x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0(lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
if (lean_obj_tag(v_a_751_) == 0)
{
lean_object* v___x_753_; 
v___x_753_ = l_List_reverse___redArg(v_a_752_);
return v___x_753_;
}
else
{
lean_object* v_head_754_; lean_object* v_tail_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_770_; 
v_head_754_ = lean_ctor_get(v_a_751_, 0);
v_tail_755_ = lean_ctor_get(v_a_751_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v_a_751_);
if (v_isSharedCheck_770_ == 0)
{
v___x_757_ = v_a_751_;
v_isShared_758_ = v_isSharedCheck_770_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_tail_755_);
lean_inc(v_head_754_);
lean_dec(v_a_751_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_770_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___y_760_; uint8_t v___x_767_; 
v___x_767_ = lean_unbox(v_head_754_);
lean_dec(v_head_754_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; 
v___x_768_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__0));
v___y_760_ = v___x_768_;
goto v___jp_759_;
}
else
{
lean_object* v___x_769_; 
v___x_769_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__1));
v___y_760_ = v___x_769_;
goto v___jp_759_;
}
v___jp_759_:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_764_; 
lean_inc_ref(v___y_760_);
v___x_761_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_761_, 0, v___y_760_);
v___x_762_ = l_Lean_MessageData_ofFormat(v___x_761_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 1, v_a_752_);
lean_ctor_set(v___x_757_, 0, v___x_762_);
v___x_764_ = v___x_757_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_a_752_);
v___x_764_ = v_reuseFailAlloc_766_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
v_a_751_ = v_tail_755_;
v_a_752_ = v___x_764_;
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
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__1));
v___x_775_ = l_Lean_MessageData_ofFormat(v___x_774_);
return v___x_775_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__3));
v___x_778_ = l_Lean_stringToMessageData(v___x_777_);
return v___x_778_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__5));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__7));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__9));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData(lean_object* v_x_788_){
_start:
{
switch(lean_obj_tag(v_x_788_))
{
case 0:
{
lean_object* v___x_789_; 
v___x_789_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2);
return v___x_789_;
}
case 1:
{
lean_object* v_prefixSize_790_; lean_object* v_suffixSize_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_808_; 
v_prefixSize_790_ = lean_ctor_get(v_x_788_, 0);
v_suffixSize_791_ = lean_ctor_get(v_x_788_, 1);
v_isSharedCheck_808_ = !lean_is_exclusive(v_x_788_);
if (v_isSharedCheck_808_ == 0)
{
v___x_793_ = v_x_788_;
v_isShared_794_ = v_isSharedCheck_808_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_suffixSize_791_);
lean_inc(v_prefixSize_790_);
lean_dec(v_x_788_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_808_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_795_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4);
v___x_796_ = l_Nat_reprFast(v_prefixSize_790_);
v___x_797_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
v___x_798_ = l_Lean_MessageData_ofFormat(v___x_797_);
if (v_isShared_794_ == 0)
{
lean_ctor_set_tag(v___x_793_, 7);
lean_ctor_set(v___x_793_, 1, v___x_798_);
lean_ctor_set(v___x_793_, 0, v___x_795_);
v___x_800_ = v___x_793_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v___x_798_);
v___x_800_ = v_reuseFailAlloc_807_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_801_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6);
v___x_802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_800_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = l_Nat_reprFast(v_suffixSize_791_);
v___x_804_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
v___x_805_ = l_Lean_MessageData_ofFormat(v___x_804_);
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_802_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
return v___x_806_;
}
}
}
case 2:
{
lean_object* v_rewritable_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v_rewritable_809_ = lean_ctor_get(v_x_788_, 0);
lean_inc_ref(v_rewritable_809_);
lean_dec_ref_known(v_x_788_, 1);
v___x_810_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8);
v___x_811_ = lean_array_to_list(v_rewritable_809_);
v___x_812_ = lean_box(0);
v___x_813_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0(v___x_811_, v___x_812_);
v___x_814_ = l_Lean_MessageData_ofList(v___x_813_);
v___x_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_810_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
return v___x_815_;
}
default: 
{
lean_object* v_thm_816_; lean_object* v_proof_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v_thm_816_ = lean_ctor_get(v_x_788_, 0);
lean_inc_ref(v_thm_816_);
lean_dec_ref_known(v_x_788_, 1);
v_proof_817_ = lean_ctor_get(v_thm_816_, 1);
lean_inc_ref(v_proof_817_);
lean_dec_ref(v_thm_816_);
v___x_818_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10);
v___x_819_ = l_Lean_MessageData_ofExpr(v_proof_817_);
v___x_820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
return v___x_820_;
}
}
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_FunInfo(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_CongrInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
