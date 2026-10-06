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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter___redArg(uint8_t v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_, lean_object* v_h__3_20_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter___redArg___boxed(lean_object* v_x_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_, lean_object* v_h__3_30_){
_start:
{
uint8_t v_x_18__boxed_31_; lean_object* v_res_32_; 
v_x_18__boxed_31_ = lean_unbox(v_x_27_);
v_res_32_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter___redArg(v_x_18__boxed_31_, v_h__1_28_, v_h__2_29_, v_h__3_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter(lean_object* v_motive_33_, uint8_t v_x_34_, lean_object* v_h__1_35_, lean_object* v_h__2_36_, lean_object* v_h__3_37_){
_start:
{
switch(v_x_34_)
{
case 0:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
lean_dec(v_h__3_37_);
lean_dec(v_h__2_36_);
v___x_38_ = lean_box(0);
v___x_39_ = lean_apply_1(v_h__1_35_, v___x_38_);
return v___x_39_;
}
case 2:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
lean_dec(v_h__3_37_);
lean_dec(v_h__1_35_);
v___x_40_ = lean_box(0);
v___x_41_ = lean_apply_1(v_h__2_36_, v___x_40_);
return v___x_41_;
}
default: 
{
lean_object* v___x_42_; lean_object* v___x_43_; 
lean_dec(v_h__2_36_);
lean_dec(v_h__1_35_);
v___x_42_ = lean_box(v_x_34_);
v___x_43_ = lean_apply_3(v_h__3_37_, v___x_42_, lean_box(0), lean_box(0));
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter___boxed(lean_object* v_motive_44_, lean_object* v_x_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_, lean_object* v_h__3_48_){
_start:
{
uint8_t v_x_33__boxed_49_; lean_object* v_res_50_; 
v_x_33__boxed_49_ = lean_unbox(v_x_45_);
v_res_50_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq_match__1_splitter(v_motive_44_, v_x_33__boxed_49_, v_h__1_46_, v_h__2_47_, v_h__3_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_go(lean_object* v_argKinds_51_, lean_object* v_i_52_){
_start:
{
lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_53_ = lean_array_get_size(v_argKinds_51_);
v___x_54_ = lean_nat_dec_lt(v_i_52_, v___x_53_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; 
lean_dec(v_i_52_);
v___x_55_ = lean_box(0);
return v___x_55_;
}
else
{
lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_56_ = lean_array_fget_borrowed(v_argKinds_51_, v_i_52_);
v___x_57_ = lean_unbox(v___x_56_);
switch(v___x_57_)
{
case 0:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_unsigned_to_nat(1u);
v___x_59_ = lean_nat_add(v_i_52_, v___x_58_);
lean_dec(v_i_52_);
v_i_52_ = v___x_59_;
goto _start;
}
case 2:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = lean_nat_add(v_i_52_, v___x_61_);
v___x_63_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_goEq(v_argKinds_51_, v_i_52_, v___x_62_);
return v___x_63_;
}
default: 
{
lean_object* v___x_64_; 
lean_dec(v_i_52_);
v___x_64_ = lean_box(0);
return v___x_64_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_go___boxed(lean_object* v_argKinds_65_, lean_object* v_i_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_go(v_argKinds_65_, v_i_66_);
lean_dec_ref(v_argKinds_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f(lean_object* v_argKinds_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f_go(v_argKinds_68_, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f___boxed(lean_object* v_argKinds_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f(v_argKinds_71_);
lean_dec_ref(v_argKinds_71_);
return v_res_72_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg(lean_object* v_xs_73_, lean_object* v_ys_74_, lean_object* v_x_75_){
_start:
{
lean_object* v_zero_76_; uint8_t v_isZero_77_; 
v_zero_76_ = lean_unsigned_to_nat(0u);
v_isZero_77_ = lean_nat_dec_eq(v_x_75_, v_zero_76_);
if (v_isZero_77_ == 1)
{
lean_dec(v_x_75_);
return v_isZero_77_;
}
else
{
lean_object* v_one_78_; lean_object* v_n_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; uint8_t v___x_83_; uint8_t v___x_84_; 
v_one_78_ = lean_unsigned_to_nat(1u);
v_n_79_ = lean_nat_sub(v_x_75_, v_one_78_);
lean_dec(v_x_75_);
v___x_80_ = lean_array_fget_borrowed(v_xs_73_, v_n_79_);
v___x_81_ = lean_array_fget_borrowed(v_ys_74_, v_n_79_);
v___x_82_ = lean_unbox(v___x_80_);
v___x_83_ = lean_unbox(v___x_81_);
v___x_84_ = l_Lean_Meta_instBEqCongrArgKind_beq(v___x_82_, v___x_83_);
if (v___x_84_ == 0)
{
lean_dec(v_n_79_);
return v___x_84_;
}
else
{
v_x_75_ = v_n_79_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg___boxed(lean_object* v_xs_86_, lean_object* v_ys_87_, lean_object* v_x_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg(v_xs_86_, v_ys_87_, v_x_88_);
lean_dec_ref(v_ys_87_);
lean_dec_ref(v_xs_86_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0(uint8_t v___y_91_, uint8_t v_a_92_, lean_object* v_as_93_, size_t v_i_94_, size_t v_stop_95_){
_start:
{
uint8_t v___x_96_; 
v___x_96_ = lean_usize_dec_eq(v_i_94_, v_stop_95_);
if (v___x_96_ == 0)
{
uint8_t v___x_97_; uint8_t v___y_99_; lean_object* v___x_103_; uint8_t v___x_104_; uint8_t v___x_105_; uint8_t v___x_106_; 
v___x_97_ = 1;
v___x_103_ = lean_array_uget_borrowed(v_as_93_, v_i_94_);
v___x_104_ = 0;
v___x_105_ = lean_unbox(v___x_103_);
v___x_106_ = l_Lean_Meta_instBEqCongrArgKind_beq(v___x_105_, v___x_104_);
if (v___x_106_ == 0)
{
v___y_99_ = v___y_91_;
goto v___jp_98_;
}
else
{
v___y_99_ = v_a_92_;
goto v___jp_98_;
}
v___jp_98_:
{
if (v___y_99_ == 0)
{
size_t v___x_100_; size_t v___x_101_; 
v___x_100_ = ((size_t)1ULL);
v___x_101_ = lean_usize_add(v_i_94_, v___x_100_);
v_i_94_ = v___x_101_;
goto _start;
}
else
{
return v___x_97_;
}
}
}
else
{
uint8_t v___x_107_; 
v___x_107_ = 0;
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0___boxed(lean_object* v___y_108_, lean_object* v_a_109_, lean_object* v_as_110_, lean_object* v_i_111_, lean_object* v_stop_112_){
_start:
{
uint8_t v___y_6083__boxed_113_; uint8_t v_a_6084__boxed_114_; size_t v_i_boxed_115_; size_t v_stop_boxed_116_; uint8_t v_res_117_; lean_object* v_r_118_; 
v___y_6083__boxed_113_ = lean_unbox(v___y_108_);
v_a_6084__boxed_114_ = lean_unbox(v_a_109_);
v_i_boxed_115_ = lean_unbox_usize(v_i_111_);
lean_dec(v_i_111_);
v_stop_boxed_116_ = lean_unbox_usize(v_stop_112_);
lean_dec(v_stop_112_);
v_res_117_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0(v___y_6083__boxed_113_, v_a_6084__boxed_114_, v_as_110_, v_i_boxed_115_, v_stop_boxed_116_);
lean_dec_ref(v_as_110_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1(size_t v_sz_119_, size_t v_i_120_, lean_object* v_bs_121_){
_start:
{
uint8_t v___x_122_; 
v___x_122_ = lean_usize_dec_lt(v_i_120_, v_sz_119_);
if (v___x_122_ == 0)
{
return v_bs_121_;
}
else
{
lean_object* v_v_123_; lean_object* v___x_124_; lean_object* v_bs_x27_125_; uint8_t v___x_126_; uint8_t v___x_127_; uint8_t v___x_128_; size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v_v_123_ = lean_array_uget(v_bs_121_, v_i_120_);
v___x_124_ = lean_unsigned_to_nat(0u);
v_bs_x27_125_ = lean_array_uset(v_bs_121_, v_i_120_, v___x_124_);
v___x_126_ = 2;
v___x_127_ = lean_unbox(v_v_123_);
lean_dec(v_v_123_);
v___x_128_ = l_Lean_Meta_instBEqCongrArgKind_beq(v___x_127_, v___x_126_);
v___x_129_ = ((size_t)1ULL);
v___x_130_ = lean_usize_add(v_i_120_, v___x_129_);
v___x_131_ = lean_box(v___x_128_);
v___x_132_ = lean_array_uset(v_bs_x27_125_, v_i_120_, v___x_131_);
v_i_120_ = v___x_130_;
v_bs_121_ = v___x_132_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1___boxed(lean_object* v_sz_134_, lean_object* v_i_135_, lean_object* v_bs_136_){
_start:
{
size_t v_sz_boxed_137_; size_t v_i_boxed_138_; lean_object* v_res_139_; 
v_sz_boxed_137_ = lean_unbox_usize(v_sz_134_);
lean_dec(v_sz_134_);
v_i_boxed_138_ = lean_unbox_usize(v_i_135_);
lean_dec(v_i_135_);
v_res_139_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1(v_sz_boxed_137_, v_i_boxed_138_, v_bs_136_);
return v_res_139_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2(uint8_t v_a_140_, lean_object* v_as_141_, size_t v_i_142_, size_t v_stop_143_){
_start:
{
uint8_t v___x_144_; 
v___x_144_ = lean_usize_dec_eq(v_i_142_, v_stop_143_);
if (v___x_144_ == 0)
{
uint8_t v___x_145_; uint8_t v___y_147_; lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_145_ = 1;
v___x_151_ = lean_array_uget_borrowed(v_as_141_, v_i_142_);
v___x_152_ = lean_unbox(v___x_151_);
switch(v___x_152_)
{
case 0:
{
v___y_147_ = v_a_140_;
goto v___jp_146_;
}
case 2:
{
v___y_147_ = v_a_140_;
goto v___jp_146_;
}
default: 
{
return v___x_145_;
}
}
v___jp_146_:
{
if (v___y_147_ == 0)
{
size_t v___x_148_; size_t v___x_149_; 
v___x_148_ = ((size_t)1ULL);
v___x_149_ = lean_usize_add(v_i_142_, v___x_148_);
v_i_142_ = v___x_149_;
goto _start;
}
else
{
return v___x_145_;
}
}
}
else
{
uint8_t v___x_153_; 
v___x_153_ = 0;
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2___boxed(lean_object* v_a_154_, lean_object* v_as_155_, lean_object* v_i_156_, lean_object* v_stop_157_){
_start:
{
uint8_t v_a_6133__boxed_158_; size_t v_i_boxed_159_; size_t v_stop_boxed_160_; uint8_t v_res_161_; lean_object* v_r_162_; 
v_a_6133__boxed_158_ = lean_unbox(v_a_154_);
v_i_boxed_159_ = lean_unbox_usize(v_i_156_);
lean_dec(v_i_156_);
v_stop_boxed_160_ = lean_unbox_usize(v_stop_157_);
lean_dec(v_stop_157_);
v_res_161_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2(v_a_6133__boxed_158_, v_as_155_, v_i_boxed_159_, v_stop_boxed_160_);
lean_dec_ref(v_as_155_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(lean_object* v_f_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v___x_169_; 
lean_inc_ref(v_f_163_);
v___x_169_ = l_Lean_Meta_isProof(v_f_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_306_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_306_ == 0)
{
v___x_172_ = v___x_169_;
v_isShared_173_ = v_isSharedCheck_306_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_169_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_306_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
uint8_t v___x_174_; 
v___x_174_ = lean_unbox(v_a_170_);
if (v___x_174_ == 0)
{
uint8_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
lean_del_object(v___x_172_);
v___x_175_ = 1;
v___x_176_ = lean_box(0);
lean_inc_ref(v_f_163_);
v___x_177_ = l_Lean_Meta_getFunInfo(v_f_163_, v___x_176_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_293_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_293_ == 0)
{
v___x_180_ = v___x_177_;
v_isShared_181_ = v_isSharedCheck_293_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_293_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; 
lean_inc_ref(v_f_163_);
v___x_182_ = l_Lean_Meta_getCongrSimpKinds(v_f_163_, v_a_178_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_284_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_284_ == 0)
{
v___x_185_ = v___x_182_;
v_isShared_186_ = v_isSharedCheck_284_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_182_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_284_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___y_193_; lean_object* v___y_194_; lean_object* v___y_195_; lean_object* v___y_196_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___y_229_; uint8_t v___x_248_; 
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = lean_array_get_size(v_a_183_);
v___x_248_ = lean_nat_dec_lt(v___x_226_, v___x_227_);
if (v___x_248_ == 0)
{
lean_dec(v_a_178_);
lean_dec_ref(v_f_163_);
v___y_229_ = v___x_175_;
goto v___jp_228_;
}
else
{
if (v___x_248_ == 0)
{
lean_dec(v_a_178_);
lean_dec_ref(v_f_163_);
v___y_229_ = v___x_175_;
goto v___jp_228_;
}
else
{
size_t v___x_249_; size_t v___x_250_; uint8_t v___x_251_; uint8_t v___x_252_; 
v___x_249_ = ((size_t)0ULL);
v___x_250_ = lean_usize_of_nat(v___x_227_);
v___x_251_ = lean_unbox(v_a_170_);
v___x_252_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2(v___x_251_, v_a_183_, v___x_249_, v___x_250_);
if (v___x_252_ == 0)
{
lean_dec(v_a_178_);
lean_dec_ref(v_f_163_);
v___y_229_ = v___x_248_;
goto v___jp_228_;
}
else
{
lean_del_object(v___x_185_);
lean_del_object(v___x_180_);
lean_dec(v_a_170_);
if (lean_obj_tag(v_f_163_) == 4)
{
lean_object* v_declName_253_; lean_object* v_us_254_; lean_object* v___x_255_; 
v_declName_253_ = lean_ctor_get(v_f_163_, 0);
v_us_254_ = lean_ctor_get(v_f_163_, 1);
lean_inc(v_us_254_);
lean_inc(v_declName_253_);
v___x_255_ = l_Lean_Meta_mkCongrSimpForConst_x3f(v_declName_253_, v_us_254_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_275_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_275_ == 0)
{
v___x_258_ = v___x_255_;
v_isShared_259_ = v_isSharedCheck_275_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_275_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
if (lean_obj_tag(v_a_256_) == 1)
{
lean_object* v_val_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_274_; 
v_val_260_ = lean_ctor_get(v_a_256_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v_a_256_);
if (v_isSharedCheck_274_ == 0)
{
v___x_262_ = v_a_256_;
v_isShared_263_ = v_isSharedCheck_274_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_val_260_);
lean_dec(v_a_256_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_274_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v_argKinds_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v_argKinds_264_ = lean_ctor_get(v_val_260_, 2);
v___x_265_ = lean_array_get_size(v_argKinds_264_);
v___x_266_ = lean_nat_dec_eq(v___x_265_, v___x_227_);
if (v___x_266_ == 0)
{
lean_del_object(v___x_262_);
lean_dec(v_val_260_);
lean_del_object(v___x_258_);
v___y_193_ = v_a_164_;
v___y_194_ = v_a_165_;
v___y_195_ = v_a_166_;
v___y_196_ = v_a_167_;
goto v___jp_192_;
}
else
{
uint8_t v___x_267_; 
v___x_267_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg(v_argKinds_264_, v_a_183_, v___x_265_);
if (v___x_267_ == 0)
{
lean_del_object(v___x_262_);
lean_dec(v_val_260_);
lean_del_object(v___x_258_);
v___y_193_ = v_a_164_;
v___y_194_ = v_a_165_;
v___y_195_ = v_a_166_;
v___y_196_ = v_a_167_;
goto v___jp_192_;
}
else
{
lean_object* v___x_269_; 
lean_dec_ref_known(v_f_163_, 2);
lean_dec(v_a_183_);
lean_dec(v_a_178_);
if (v_isShared_263_ == 0)
{
lean_ctor_set_tag(v___x_262_, 3);
v___x_269_ = v___x_262_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_val_260_);
v___x_269_ = v_reuseFailAlloc_273_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
lean_object* v___x_271_; 
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 0, v___x_269_);
v___x_271_ = v___x_258_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
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
else
{
lean_del_object(v___x_258_);
lean_dec(v_a_256_);
v___y_193_ = v_a_164_;
v___y_194_ = v_a_165_;
v___y_195_ = v_a_166_;
v___y_196_ = v_a_167_;
goto v___jp_192_;
}
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_dec_ref_known(v_f_163_, 2);
lean_dec(v_a_183_);
lean_dec(v_a_178_);
v_a_276_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_255_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_255_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
else
{
v___y_193_ = v_a_164_;
v___y_194_ = v_a_165_;
v___y_195_ = v_a_166_;
v___y_196_ = v_a_167_;
goto v___jp_192_;
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
v___jp_192_:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Meta_mkCongrSimpCore_x3f(v_f_163_, v_a_178_, v_a_183_, v___x_175_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_217_; 
v_a_198_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_217_ == 0)
{
v___x_200_ = v___x_197_;
v_isShared_201_ = v_isSharedCheck_217_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_197_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_217_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
if (lean_obj_tag(v_a_198_) == 1)
{
lean_object* v_val_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_212_; 
v_val_202_ = lean_ctor_get(v_a_198_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v_a_198_);
if (v_isSharedCheck_212_ == 0)
{
v___x_204_ = v_a_198_;
v_isShared_205_ = v_isSharedCheck_212_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_val_202_);
lean_dec(v_a_198_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_212_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
lean_ctor_set_tag(v___x_204_, 3);
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_val_202_);
v___x_207_ = v_reuseFailAlloc_211_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_209_; 
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 0, v___x_207_);
v___x_209_ = v___x_200_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
else
{
lean_object* v___x_213_; lean_object* v___x_215_; 
lean_dec(v_a_198_);
v___x_213_ = lean_box(0);
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 0, v___x_213_);
v___x_215_ = v___x_200_;
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
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
v_a_218_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_197_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_197_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
v___jp_228_:
{
uint8_t v___x_230_; 
v___x_230_ = lean_nat_dec_lt(v___x_226_, v___x_227_);
if (v___x_230_ == 0)
{
lean_dec(v_a_183_);
lean_del_object(v___x_180_);
lean_dec(v_a_170_);
goto v___jp_187_;
}
else
{
if (v___x_230_ == 0)
{
lean_dec(v_a_183_);
lean_del_object(v___x_180_);
lean_dec(v_a_170_);
goto v___jp_187_;
}
else
{
size_t v___x_231_; size_t v___x_232_; uint8_t v___x_233_; uint8_t v___x_234_; 
v___x_231_ = ((size_t)0ULL);
v___x_232_ = lean_usize_of_nat(v___x_227_);
v___x_233_ = lean_unbox(v_a_170_);
lean_dec(v_a_170_);
v___x_234_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0(v___y_229_, v___x_233_, v_a_183_, v___x_231_, v___x_232_);
if (v___x_234_ == 0)
{
lean_dec(v_a_183_);
lean_del_object(v___x_180_);
goto v___jp_187_;
}
else
{
lean_object* v___x_235_; 
lean_del_object(v___x_185_);
v___x_235_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f(v_a_183_);
if (lean_obj_tag(v___x_235_) == 1)
{
lean_object* v_val_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_240_; 
lean_dec(v_a_183_);
v_val_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_val_236_);
lean_dec_ref_known(v___x_235_, 1);
v___x_237_ = lean_nat_sub(v___x_227_, v_val_236_);
v___x_238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_238_, 0, v_val_236_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_238_);
v___x_240_ = v___x_180_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
else
{
size_t v_sz_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
lean_dec(v___x_235_);
v_sz_242_ = lean_array_size(v_a_183_);
v___x_243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1(v_sz_242_, v___x_231_, v_a_183_);
v___x_244_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_244_);
v___x_246_ = v___x_180_;
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
}
}
}
}
}
}
else
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
lean_del_object(v___x_180_);
lean_dec(v_a_178_);
lean_dec(v_a_170_);
lean_dec_ref(v_f_163_);
v_a_285_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_182_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_182_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
else
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
lean_dec(v_a_170_);
lean_dec_ref(v_f_163_);
v_a_294_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_177_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_177_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
else
{
lean_object* v___x_302_; lean_object* v___x_304_; 
lean_dec(v_a_170_);
lean_dec_ref(v_f_163_);
v___x_302_ = lean_box(0);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_302_);
v___x_304_ = v___x_172_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
lean_dec_ref(v_f_163_);
v_a_307_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_169_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_169_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg___boxed(lean_object* v_f_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(v_f_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo(lean_object* v_f_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(v_f_322_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___boxed(lean_object* v_f_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo(v_f_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
return v_res_339_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3(lean_object* v_xs_340_, lean_object* v_ys_341_, lean_object* v_hsz_342_, lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
uint8_t v___x_345_; 
v___x_345_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg(v_xs_340_, v_ys_341_, v_x_343_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___boxed(lean_object* v_xs_346_, lean_object* v_ys_347_, lean_object* v_hsz_348_, lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
uint8_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3(v_xs_346_, v_ys_347_, v_hsz_348_, v_x_349_, v_x_350_);
lean_dec_ref(v_ys_347_);
lean_dec_ref(v_xs_346_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_353_, lean_object* v_x_354_, lean_object* v_x_355_, lean_object* v_x_356_){
_start:
{
lean_object* v_ks_357_; lean_object* v_vs_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_384_; 
v_ks_357_ = lean_ctor_get(v_x_353_, 0);
v_vs_358_ = lean_ctor_get(v_x_353_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v_x_353_);
if (v_isSharedCheck_384_ == 0)
{
v___x_360_ = v_x_353_;
v_isShared_361_ = v_isSharedCheck_384_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_vs_358_);
lean_inc(v_ks_357_);
lean_dec(v_x_353_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_384_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = lean_array_get_size(v_ks_357_);
v___x_363_ = lean_nat_dec_lt(v_x_354_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_367_; 
lean_dec(v_x_354_);
v___x_364_ = lean_array_push(v_ks_357_, v_x_355_);
v___x_365_ = lean_array_push(v_vs_358_, v_x_356_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v___x_365_);
lean_ctor_set(v___x_360_, 0, v___x_364_);
v___x_367_ = v___x_360_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_364_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
else
{
lean_object* v_k_x27_369_; size_t v___x_370_; size_t v___x_371_; uint8_t v___x_372_; 
v_k_x27_369_ = lean_array_fget_borrowed(v_ks_357_, v_x_354_);
v___x_370_ = lean_ptr_addr(v_x_355_);
v___x_371_ = lean_ptr_addr(v_k_x27_369_);
v___x_372_ = lean_usize_dec_eq(v___x_370_, v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_374_; 
if (v_isShared_361_ == 0)
{
v___x_374_ = v___x_360_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_ks_357_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_vs_358_);
v___x_374_ = v_reuseFailAlloc_378_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_unsigned_to_nat(1u);
v___x_376_ = lean_nat_add(v_x_354_, v___x_375_);
lean_dec(v_x_354_);
v_x_353_ = v___x_374_;
v_x_354_ = v___x_376_;
goto _start;
}
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_379_ = lean_array_fset(v_ks_357_, v_x_354_, v_x_355_);
v___x_380_ = lean_array_fset(v_vs_358_, v_x_354_, v_x_356_);
lean_dec(v_x_354_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v___x_380_);
lean_ctor_set(v___x_360_, 0, v___x_379_);
v___x_382_ = v___x_360_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4___redArg(lean_object* v_n_385_, lean_object* v_k_386_, lean_object* v_v_387_){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_unsigned_to_nat(0u);
v___x_389_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5___redArg(v_n_385_, v___x_388_, v_k_386_, v_v_387_);
return v___x_389_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(lean_object* v_x_391_, size_t v_x_392_, size_t v_x_393_, lean_object* v_x_394_, lean_object* v_x_395_){
_start:
{
if (lean_obj_tag(v_x_391_) == 0)
{
lean_object* v_es_396_; size_t v___x_397_; size_t v___x_398_; lean_object* v_j_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v_es_396_ = lean_ctor_get(v_x_391_, 0);
v___x_397_ = ((size_t)31ULL);
v___x_398_ = lean_usize_land(v_x_392_, v___x_397_);
v_j_399_ = lean_usize_to_nat(v___x_398_);
v___x_400_ = lean_array_get_size(v_es_396_);
v___x_401_ = lean_nat_dec_lt(v_j_399_, v___x_400_);
if (v___x_401_ == 0)
{
lean_dec(v_j_399_);
lean_dec(v_x_395_);
lean_dec_ref(v_x_394_);
return v_x_391_;
}
else
{
lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_442_; 
lean_inc_ref(v_es_396_);
v_isSharedCheck_442_ = !lean_is_exclusive(v_x_391_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; 
v_unused_443_ = lean_ctor_get(v_x_391_, 0);
lean_dec(v_unused_443_);
v___x_403_ = v_x_391_;
v_isShared_404_ = v_isSharedCheck_442_;
goto v_resetjp_402_;
}
else
{
lean_dec(v_x_391_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_442_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v_v_405_; lean_object* v___x_406_; lean_object* v_xs_x27_407_; lean_object* v___y_409_; 
v_v_405_ = lean_array_fget(v_es_396_, v_j_399_);
v___x_406_ = lean_box(0);
v_xs_x27_407_ = lean_array_fset(v_es_396_, v_j_399_, v___x_406_);
switch(lean_obj_tag(v_v_405_))
{
case 0:
{
lean_object* v_key_414_; lean_object* v_val_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_427_; 
v_key_414_ = lean_ctor_get(v_v_405_, 0);
v_val_415_ = lean_ctor_get(v_v_405_, 1);
v_isSharedCheck_427_ = !lean_is_exclusive(v_v_405_);
if (v_isSharedCheck_427_ == 0)
{
v___x_417_ = v_v_405_;
v_isShared_418_ = v_isSharedCheck_427_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_val_415_);
lean_inc(v_key_414_);
lean_dec(v_v_405_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_427_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
size_t v___x_419_; size_t v___x_420_; uint8_t v___x_421_; 
v___x_419_ = lean_ptr_addr(v_x_394_);
v___x_420_ = lean_ptr_addr(v_key_414_);
v___x_421_ = lean_usize_dec_eq(v___x_419_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; 
lean_del_object(v___x_417_);
v___x_422_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_414_, v_val_415_, v_x_394_, v_x_395_);
v___x_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
v___y_409_ = v___x_423_;
goto v___jp_408_;
}
else
{
lean_object* v___x_425_; 
lean_dec(v_val_415_);
lean_dec(v_key_414_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v_x_395_);
lean_ctor_set(v___x_417_, 0, v_x_394_);
v___x_425_ = v___x_417_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_x_394_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_x_395_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
v___y_409_ = v___x_425_;
goto v___jp_408_;
}
}
}
}
case 1:
{
lean_object* v_node_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_440_; 
v_node_428_ = lean_ctor_get(v_v_405_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v_v_405_);
if (v_isSharedCheck_440_ == 0)
{
v___x_430_ = v_v_405_;
v_isShared_431_ = v_isSharedCheck_440_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_node_428_);
lean_dec(v_v_405_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_440_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
size_t v___x_432_; size_t v___x_433_; size_t v___x_434_; size_t v___x_435_; lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_432_ = ((size_t)5ULL);
v___x_433_ = lean_usize_shift_right(v_x_392_, v___x_432_);
v___x_434_ = ((size_t)1ULL);
v___x_435_ = lean_usize_add(v_x_393_, v___x_434_);
v___x_436_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_node_428_, v___x_433_, v___x_435_, v_x_394_, v_x_395_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_436_);
v___x_438_ = v___x_430_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
v___y_409_ = v___x_438_;
goto v___jp_408_;
}
}
}
default: 
{
lean_object* v___x_441_; 
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v_x_394_);
lean_ctor_set(v___x_441_, 1, v_x_395_);
v___y_409_ = v___x_441_;
goto v___jp_408_;
}
}
v___jp_408_:
{
lean_object* v___x_410_; lean_object* v___x_412_; 
v___x_410_ = lean_array_fset(v_xs_x27_407_, v_j_399_, v___y_409_);
lean_dec(v_j_399_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_410_);
v___x_412_ = v___x_403_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_410_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
else
{
lean_object* v_ks_444_; lean_object* v_vs_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_463_; 
v_ks_444_ = lean_ctor_get(v_x_391_, 0);
v_vs_445_ = lean_ctor_get(v_x_391_, 1);
v_isSharedCheck_463_ = !lean_is_exclusive(v_x_391_);
if (v_isSharedCheck_463_ == 0)
{
v___x_447_ = v_x_391_;
v_isShared_448_ = v_isSharedCheck_463_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_vs_445_);
lean_inc(v_ks_444_);
lean_dec(v_x_391_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_463_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_ks_444_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_vs_445_);
v___x_450_ = v_reuseFailAlloc_462_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v_newNode_451_; size_t v___x_452_; uint8_t v___x_453_; 
v_newNode_451_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4___redArg(v___x_450_, v_x_394_, v_x_395_);
v___x_452_ = ((size_t)7ULL);
v___x_453_ = lean_usize_dec_le(v___x_452_, v_x_393_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_454_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_451_);
v___x_455_ = lean_unsigned_to_nat(4u);
v___x_456_ = lean_nat_dec_lt(v___x_454_, v___x_455_);
lean_dec(v___x_454_);
if (v___x_456_ == 0)
{
lean_object* v_ks_457_; lean_object* v_vs_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v_ks_457_ = lean_ctor_get(v_newNode_451_, 0);
lean_inc_ref(v_ks_457_);
v_vs_458_ = lean_ctor_get(v_newNode_451_, 1);
lean_inc_ref(v_vs_458_);
lean_dec_ref(v_newNode_451_);
v___x_459_ = lean_unsigned_to_nat(0u);
v___x_460_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0);
v___x_461_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(v_x_393_, v_ks_457_, v_vs_458_, v___x_459_, v___x_460_);
lean_dec_ref(v_vs_458_);
lean_dec_ref(v_ks_457_);
return v___x_461_;
}
else
{
return v_newNode_451_;
}
}
else
{
return v_newNode_451_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(size_t v_depth_464_, lean_object* v_keys_465_, lean_object* v_vals_466_, lean_object* v_i_467_, lean_object* v_entries_468_){
_start:
{
lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_469_ = lean_array_get_size(v_keys_465_);
v___x_470_ = lean_nat_dec_lt(v_i_467_, v___x_469_);
if (v___x_470_ == 0)
{
lean_dec(v_i_467_);
return v_entries_468_;
}
else
{
lean_object* v_k_471_; lean_object* v_v_472_; size_t v___x_473_; size_t v___x_474_; size_t v___x_475_; uint64_t v___x_476_; size_t v_h_477_; size_t v___x_478_; lean_object* v___x_479_; size_t v___x_480_; size_t v___x_481_; size_t v___x_482_; size_t v_h_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_k_471_ = lean_array_fget_borrowed(v_keys_465_, v_i_467_);
v_v_472_ = lean_array_fget_borrowed(v_vals_466_, v_i_467_);
v___x_473_ = lean_ptr_addr(v_k_471_);
v___x_474_ = ((size_t)3ULL);
v___x_475_ = lean_usize_shift_right(v___x_473_, v___x_474_);
v___x_476_ = lean_usize_to_uint64(v___x_475_);
v_h_477_ = lean_uint64_to_usize(v___x_476_);
v___x_478_ = ((size_t)5ULL);
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_480_ = ((size_t)1ULL);
v___x_481_ = lean_usize_sub(v_depth_464_, v___x_480_);
v___x_482_ = lean_usize_mul(v___x_478_, v___x_481_);
v_h_483_ = lean_usize_shift_right(v_h_477_, v___x_482_);
v___x_484_ = lean_nat_add(v_i_467_, v___x_479_);
lean_dec(v_i_467_);
lean_inc(v_v_472_);
lean_inc(v_k_471_);
v___x_485_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_entries_468_, v_h_483_, v_depth_464_, v_k_471_, v_v_472_);
v_i_467_ = v___x_484_;
v_entries_468_ = v___x_485_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_487_, lean_object* v_keys_488_, lean_object* v_vals_489_, lean_object* v_i_490_, lean_object* v_entries_491_){
_start:
{
size_t v_depth_boxed_492_; lean_object* v_res_493_; 
v_depth_boxed_492_ = lean_unbox_usize(v_depth_487_);
lean_dec(v_depth_487_);
v_res_493_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(v_depth_boxed_492_, v_keys_488_, v_vals_489_, v_i_490_, v_entries_491_);
lean_dec_ref(v_vals_489_);
lean_dec_ref(v_keys_488_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___boxed(lean_object* v_x_494_, lean_object* v_x_495_, lean_object* v_x_496_, lean_object* v_x_497_, lean_object* v_x_498_){
_start:
{
size_t v_x_2545__boxed_499_; size_t v_x_2546__boxed_500_; lean_object* v_res_501_; 
v_x_2545__boxed_499_ = lean_unbox_usize(v_x_495_);
lean_dec(v_x_495_);
v_x_2546__boxed_500_ = lean_unbox_usize(v_x_496_);
lean_dec(v_x_496_);
v_res_501_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_x_494_, v_x_2545__boxed_499_, v_x_2546__boxed_500_, v_x_497_, v_x_498_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1___redArg(lean_object* v_x_502_, lean_object* v_x_503_, lean_object* v_x_504_){
_start:
{
size_t v___x_505_; size_t v___x_506_; size_t v___x_507_; uint64_t v___x_508_; size_t v___x_509_; size_t v___x_510_; lean_object* v___x_511_; 
v___x_505_ = lean_ptr_addr(v_x_503_);
v___x_506_ = ((size_t)3ULL);
v___x_507_ = lean_usize_shift_right(v___x_505_, v___x_506_);
v___x_508_ = lean_usize_to_uint64(v___x_507_);
v___x_509_ = lean_uint64_to_usize(v___x_508_);
v___x_510_ = ((size_t)1ULL);
v___x_511_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_x_502_, v___x_509_, v___x_510_, v_x_503_, v_x_504_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_512_, lean_object* v_vals_513_, lean_object* v_i_514_, lean_object* v_k_515_){
_start:
{
lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_516_ = lean_array_get_size(v_keys_512_);
v___x_517_ = lean_nat_dec_lt(v_i_514_, v___x_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; 
lean_dec(v_i_514_);
v___x_518_ = lean_box(0);
return v___x_518_;
}
else
{
lean_object* v_k_x27_519_; size_t v___x_520_; size_t v___x_521_; uint8_t v___x_522_; 
v_k_x27_519_ = lean_array_fget_borrowed(v_keys_512_, v_i_514_);
v___x_520_ = lean_ptr_addr(v_k_515_);
v___x_521_ = lean_ptr_addr(v_k_x27_519_);
v___x_522_ = lean_usize_dec_eq(v___x_520_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_add(v_i_514_, v___x_523_);
lean_dec(v_i_514_);
v_i_514_ = v___x_524_;
goto _start;
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_array_fget_borrowed(v_vals_513_, v_i_514_);
lean_dec(v_i_514_);
lean_inc(v___x_526_);
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_528_, lean_object* v_vals_529_, lean_object* v_i_530_, lean_object* v_k_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(v_keys_528_, v_vals_529_, v_i_530_, v_k_531_);
lean_dec_ref(v_k_531_);
lean_dec_ref(v_vals_529_);
lean_dec_ref(v_keys_528_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(lean_object* v_x_533_, size_t v_x_534_, lean_object* v_x_535_){
_start:
{
if (lean_obj_tag(v_x_533_) == 0)
{
lean_object* v_es_536_; lean_object* v___x_537_; size_t v___x_538_; size_t v___x_539_; lean_object* v_j_540_; lean_object* v___x_541_; 
v_es_536_ = lean_ctor_get(v_x_533_, 0);
v___x_537_ = lean_box(2);
v___x_538_ = ((size_t)31ULL);
v___x_539_ = lean_usize_land(v_x_534_, v___x_538_);
v_j_540_ = lean_usize_to_nat(v___x_539_);
v___x_541_ = lean_array_get_borrowed(v___x_537_, v_es_536_, v_j_540_);
lean_dec(v_j_540_);
switch(lean_obj_tag(v___x_541_))
{
case 0:
{
lean_object* v_key_542_; lean_object* v_val_543_; size_t v___x_544_; size_t v___x_545_; uint8_t v___x_546_; 
v_key_542_ = lean_ctor_get(v___x_541_, 0);
v_val_543_ = lean_ctor_get(v___x_541_, 1);
v___x_544_ = lean_ptr_addr(v_x_535_);
v___x_545_ = lean_ptr_addr(v_key_542_);
v___x_546_ = lean_usize_dec_eq(v___x_544_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; 
v___x_547_ = lean_box(0);
return v___x_547_;
}
else
{
lean_object* v___x_548_; 
lean_inc(v_val_543_);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v_val_543_);
return v___x_548_;
}
}
case 1:
{
lean_object* v_node_549_; size_t v___x_550_; size_t v___x_551_; 
v_node_549_ = lean_ctor_get(v___x_541_, 0);
v___x_550_ = ((size_t)5ULL);
v___x_551_ = lean_usize_shift_right(v_x_534_, v___x_550_);
v_x_533_ = v_node_549_;
v_x_534_ = v___x_551_;
goto _start;
}
default: 
{
lean_object* v___x_553_; 
v___x_553_ = lean_box(0);
return v___x_553_;
}
}
}
else
{
lean_object* v_ks_554_; lean_object* v_vs_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_ks_554_ = lean_ctor_get(v_x_533_, 0);
v_vs_555_ = lean_ctor_get(v_x_533_, 1);
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(v_ks_554_, v_vs_555_, v___x_556_, v_x_535_);
return v___x_557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg___boxed(lean_object* v_x_558_, lean_object* v_x_559_, lean_object* v_x_560_){
_start:
{
size_t v_x_2746__boxed_561_; lean_object* v_res_562_; 
v_x_2746__boxed_561_ = lean_unbox_usize(v_x_559_);
lean_dec(v_x_559_);
v_res_562_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(v_x_558_, v_x_2746__boxed_561_, v_x_560_);
lean_dec_ref(v_x_560_);
lean_dec_ref(v_x_558_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(lean_object* v_x_563_, lean_object* v_x_564_){
_start:
{
size_t v___x_565_; size_t v___x_566_; size_t v___x_567_; uint64_t v___x_568_; size_t v___x_569_; lean_object* v___x_570_; 
v___x_565_ = lean_ptr_addr(v_x_564_);
v___x_566_ = ((size_t)3ULL);
v___x_567_ = lean_usize_shift_right(v___x_565_, v___x_566_);
v___x_568_ = lean_usize_to_uint64(v___x_567_);
v___x_569_ = lean_uint64_to_usize(v___x_568_);
v___x_570_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(v_x_563_, v___x_569_, v_x_564_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg___boxed(lean_object* v_x_571_, lean_object* v_x_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(v_x_571_, v_x_572_);
lean_dec_ref(v_x_572_);
lean_dec_ref(v_x_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCongrInfo___redArg(lean_object* v_f_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v___x_581_; lean_object* v_congrInfo_582_; lean_object* v___x_583_; 
v___x_581_ = lean_st_ref_get(v_a_575_);
v_congrInfo_582_ = lean_ctor_get(v___x_581_, 6);
lean_inc_ref(v_congrInfo_582_);
lean_dec(v___x_581_);
v___x_583_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(v_congrInfo_582_, v_f_574_);
lean_dec_ref(v_congrInfo_582_);
if (lean_obj_tag(v___x_583_) == 1)
{
lean_object* v_val_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
lean_dec_ref(v_f_574_);
v_val_584_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_583_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_val_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set_tag(v___x_586_, 0);
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_val_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
else
{
lean_object* v___x_592_; 
lean_dec(v___x_583_);
lean_inc_ref(v_f_574_);
v___x_592_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(v_f_574_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_623_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_623_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_623_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_623_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v_share_598_; lean_object* v_maxFVar_599_; lean_object* v_proofInstInfo_600_; lean_object* v_proofInstInfoFVar_601_; lean_object* v_inferType_602_; lean_object* v_getLevel_603_; lean_object* v_congrInfo_604_; lean_object* v_defEqI_605_; lean_object* v_extensions_606_; lean_object* v_issues_607_; lean_object* v_canon_608_; lean_object* v_instanceOverrides_609_; uint8_t v_debug_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_622_; 
v___x_597_ = lean_st_ref_take(v_a_575_);
v_share_598_ = lean_ctor_get(v___x_597_, 0);
v_maxFVar_599_ = lean_ctor_get(v___x_597_, 1);
v_proofInstInfo_600_ = lean_ctor_get(v___x_597_, 2);
v_proofInstInfoFVar_601_ = lean_ctor_get(v___x_597_, 3);
v_inferType_602_ = lean_ctor_get(v___x_597_, 4);
v_getLevel_603_ = lean_ctor_get(v___x_597_, 5);
v_congrInfo_604_ = lean_ctor_get(v___x_597_, 6);
v_defEqI_605_ = lean_ctor_get(v___x_597_, 7);
v_extensions_606_ = lean_ctor_get(v___x_597_, 8);
v_issues_607_ = lean_ctor_get(v___x_597_, 9);
v_canon_608_ = lean_ctor_get(v___x_597_, 10);
v_instanceOverrides_609_ = lean_ctor_get(v___x_597_, 11);
v_debug_610_ = lean_ctor_get_uint8(v___x_597_, sizeof(void*)*12);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_622_ == 0)
{
v___x_612_ = v___x_597_;
v_isShared_613_ = v_isSharedCheck_622_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_instanceOverrides_609_);
lean_inc(v_canon_608_);
lean_inc(v_issues_607_);
lean_inc(v_extensions_606_);
lean_inc(v_defEqI_605_);
lean_inc(v_congrInfo_604_);
lean_inc(v_getLevel_603_);
lean_inc(v_inferType_602_);
lean_inc(v_proofInstInfoFVar_601_);
lean_inc(v_proofInstInfo_600_);
lean_inc(v_maxFVar_599_);
lean_inc(v_share_598_);
lean_dec(v___x_597_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_622_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_614_; lean_object* v___x_616_; 
lean_inc(v_a_593_);
v___x_614_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1___redArg(v_congrInfo_604_, v_f_574_, v_a_593_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 6, v___x_614_);
v___x_616_ = v___x_612_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 12, 1);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_share_598_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_maxFVar_599_);
lean_ctor_set(v_reuseFailAlloc_621_, 2, v_proofInstInfo_600_);
lean_ctor_set(v_reuseFailAlloc_621_, 3, v_proofInstInfoFVar_601_);
lean_ctor_set(v_reuseFailAlloc_621_, 4, v_inferType_602_);
lean_ctor_set(v_reuseFailAlloc_621_, 5, v_getLevel_603_);
lean_ctor_set(v_reuseFailAlloc_621_, 6, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_621_, 7, v_defEqI_605_);
lean_ctor_set(v_reuseFailAlloc_621_, 8, v_extensions_606_);
lean_ctor_set(v_reuseFailAlloc_621_, 9, v_issues_607_);
lean_ctor_set(v_reuseFailAlloc_621_, 10, v_canon_608_);
lean_ctor_set(v_reuseFailAlloc_621_, 11, v_instanceOverrides_609_);
lean_ctor_set_uint8(v_reuseFailAlloc_621_, sizeof(void*)*12, v_debug_610_);
v___x_616_ = v_reuseFailAlloc_621_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_617_ = lean_st_ref_put(v_a_575_, v___x_616_);
if (v_isShared_596_ == 0)
{
v___x_619_ = v___x_595_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_593_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_574_);
return v___x_592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCongrInfo___redArg___boxed(lean_object* v_f_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_Meta_Sym_getCongrInfo___redArg(v_f_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
lean_dec(v_a_629_);
lean_dec_ref(v_a_628_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCongrInfo(lean_object* v_f_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_Meta_Sym_getCongrInfo___redArg(v_f_632_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCongrInfo___boxed(lean_object* v_f_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lean_Meta_Sym_getCongrInfo(v_f_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0(lean_object* v_00_u03b2_650_, lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(v_x_651_, v_x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___boxed(lean_object* v_00_u03b2_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0(v_00_u03b2_654_, v_x_655_, v_x_656_);
lean_dec_ref(v_x_656_);
lean_dec_ref(v_x_655_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1(lean_object* v_00_u03b2_658_, lean_object* v_x_659_, lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1___redArg(v_x_659_, v_x_660_, v_x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0(lean_object* v_00_u03b2_663_, lean_object* v_x_664_, size_t v_x_665_, lean_object* v_x_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(v_x_664_, v_x_665_, v_x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___boxed(lean_object* v_00_u03b2_668_, lean_object* v_x_669_, lean_object* v_x_670_, lean_object* v_x_671_){
_start:
{
size_t v_x_2898__boxed_672_; lean_object* v_res_673_; 
v_x_2898__boxed_672_ = lean_unbox_usize(v_x_670_);
lean_dec(v_x_670_);
v_res_673_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0(v_00_u03b2_668_, v_x_669_, v_x_2898__boxed_672_, v_x_671_);
lean_dec_ref(v_x_671_);
lean_dec_ref(v_x_669_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2(lean_object* v_00_u03b2_674_, lean_object* v_x_675_, size_t v_x_676_, size_t v_x_677_, lean_object* v_x_678_, lean_object* v_x_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_x_675_, v_x_676_, v_x_677_, v_x_678_, v_x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___boxed(lean_object* v_00_u03b2_681_, lean_object* v_x_682_, lean_object* v_x_683_, lean_object* v_x_684_, lean_object* v_x_685_, lean_object* v_x_686_){
_start:
{
size_t v_x_2909__boxed_687_; size_t v_x_2910__boxed_688_; lean_object* v_res_689_; 
v_x_2909__boxed_687_ = lean_unbox_usize(v_x_683_);
lean_dec(v_x_683_);
v_x_2910__boxed_688_ = lean_unbox_usize(v_x_684_);
lean_dec(v_x_684_);
v_res_689_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2(v_00_u03b2_681_, v_x_682_, v_x_2909__boxed_687_, v_x_2910__boxed_688_, v_x_685_, v_x_686_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_690_, lean_object* v_keys_691_, lean_object* v_vals_692_, lean_object* v_heq_693_, lean_object* v_i_694_, lean_object* v_k_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(v_keys_691_, v_vals_692_, v_i_694_, v_k_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_697_, lean_object* v_keys_698_, lean_object* v_vals_699_, lean_object* v_heq_700_, lean_object* v_i_701_, lean_object* v_k_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1(v_00_u03b2_697_, v_keys_698_, v_vals_699_, v_heq_700_, v_i_701_, v_k_702_);
lean_dec_ref(v_k_702_);
lean_dec_ref(v_vals_699_);
lean_dec_ref(v_keys_698_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_704_, lean_object* v_n_705_, lean_object* v_k_706_, lean_object* v_v_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4___redArg(v_n_705_, v_k_706_, v_v_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_709_, size_t v_depth_710_, lean_object* v_keys_711_, lean_object* v_vals_712_, lean_object* v_heq_713_, lean_object* v_i_714_, lean_object* v_entries_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(v_depth_710_, v_keys_711_, v_vals_712_, v_i_714_, v_entries_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_717_, lean_object* v_depth_718_, lean_object* v_keys_719_, lean_object* v_vals_720_, lean_object* v_heq_721_, lean_object* v_i_722_, lean_object* v_entries_723_){
_start:
{
size_t v_depth_boxed_724_; lean_object* v_res_725_; 
v_depth_boxed_724_ = lean_unbox_usize(v_depth_718_);
lean_dec(v_depth_718_);
v_res_725_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5(v_00_u03b2_717_, v_depth_boxed_724_, v_keys_719_, v_vals_720_, v_heq_721_, v_i_722_, v_entries_723_);
lean_dec_ref(v_vals_720_);
lean_dec_ref(v_keys_719_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_726_, lean_object* v_x_727_, lean_object* v_x_728_, lean_object* v_x_729_, lean_object* v_x_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5___redArg(v_x_727_, v_x_728_, v_x_729_, v_x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0(lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
if (lean_obj_tag(v_a_734_) == 0)
{
lean_object* v___x_736_; 
v___x_736_ = l_List_reverse___redArg(v_a_735_);
return v___x_736_;
}
else
{
lean_object* v_head_737_; lean_object* v_tail_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_753_; 
v_head_737_ = lean_ctor_get(v_a_734_, 0);
v_tail_738_ = lean_ctor_get(v_a_734_, 1);
v_isSharedCheck_753_ = !lean_is_exclusive(v_a_734_);
if (v_isSharedCheck_753_ == 0)
{
v___x_740_ = v_a_734_;
v_isShared_741_ = v_isSharedCheck_753_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_tail_738_);
lean_inc(v_head_737_);
lean_dec(v_a_734_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_753_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___y_743_; uint8_t v___x_750_; 
v___x_750_ = lean_unbox(v_head_737_);
lean_dec(v_head_737_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; 
v___x_751_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__0));
v___y_743_ = v___x_751_;
goto v___jp_742_;
}
else
{
lean_object* v___x_752_; 
v___x_752_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__1));
v___y_743_ = v___x_752_;
goto v___jp_742_;
}
v___jp_742_:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
lean_inc_ref(v___y_743_);
v___x_744_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_744_, 0, v___y_743_);
v___x_745_ = l_Lean_MessageData_ofFormat(v___x_744_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 1, v_a_735_);
lean_ctor_set(v___x_740_, 0, v___x_745_);
v___x_747_ = v___x_740_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_a_735_);
v___x_747_ = v_reuseFailAlloc_749_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
v_a_734_ = v_tail_738_;
v_a_735_ = v___x_747_;
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
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__1));
v___x_758_ = l_Lean_MessageData_ofFormat(v___x_757_);
return v___x_758_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__3));
v___x_761_ = l_Lean_stringToMessageData(v___x_760_);
return v___x_761_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__5));
v___x_764_ = l_Lean_stringToMessageData(v___x_763_);
return v___x_764_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__7));
v___x_767_ = l_Lean_stringToMessageData(v___x_766_);
return v___x_767_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__9));
v___x_770_ = l_Lean_stringToMessageData(v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData(lean_object* v_x_771_){
_start:
{
switch(lean_obj_tag(v_x_771_))
{
case 0:
{
lean_object* v___x_772_; 
v___x_772_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2);
return v___x_772_;
}
case 1:
{
lean_object* v_prefixSize_773_; lean_object* v_suffixSize_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_791_; 
v_prefixSize_773_ = lean_ctor_get(v_x_771_, 0);
v_suffixSize_774_ = lean_ctor_get(v_x_771_, 1);
v_isSharedCheck_791_ = !lean_is_exclusive(v_x_771_);
if (v_isSharedCheck_791_ == 0)
{
v___x_776_ = v_x_771_;
v_isShared_777_ = v_isSharedCheck_791_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_suffixSize_774_);
lean_inc(v_prefixSize_773_);
lean_dec(v_x_771_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_791_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_778_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4);
v___x_779_ = l_Nat_reprFast(v_prefixSize_773_);
v___x_780_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
v___x_781_ = l_Lean_MessageData_ofFormat(v___x_780_);
if (v_isShared_777_ == 0)
{
lean_ctor_set_tag(v___x_776_, 7);
lean_ctor_set(v___x_776_, 1, v___x_781_);
lean_ctor_set(v___x_776_, 0, v___x_778_);
v___x_783_ = v___x_776_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_781_);
v___x_783_ = v_reuseFailAlloc_790_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_784_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6);
v___x_785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = l_Nat_reprFast(v_suffixSize_774_);
v___x_787_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
v___x_788_ = l_Lean_MessageData_ofFormat(v___x_787_);
v___x_789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_785_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
return v___x_789_;
}
}
}
case 2:
{
lean_object* v_rewritable_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_rewritable_792_ = lean_ctor_get(v_x_771_, 0);
lean_inc_ref(v_rewritable_792_);
lean_dec_ref_known(v_x_771_, 1);
v___x_793_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8);
v___x_794_ = lean_array_to_list(v_rewritable_792_);
v___x_795_ = lean_box(0);
v___x_796_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0(v___x_794_, v___x_795_);
v___x_797_ = l_Lean_MessageData_ofList(v___x_796_);
v___x_798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_793_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
return v___x_798_;
}
default: 
{
lean_object* v_thm_799_; lean_object* v_proof_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_thm_799_ = lean_ctor_get(v_x_771_, 0);
lean_inc_ref(v_thm_799_);
lean_dec_ref_known(v_x_771_, 1);
v_proof_800_ = lean_ctor_get(v_thm_799_, 1);
lean_inc_ref(v_proof_800_);
lean_dec_ref(v_thm_799_);
v___x_801_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10);
v___x_802_ = l_Lean_MessageData_ofExpr(v_proof_800_);
v___x_803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_801_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
return v___x_803_;
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
