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
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getCongrSimpKinds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrSimpCore_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Meta_instBEqCongrArgKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_mkCongrSimpForConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___closed__0;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2(lean_object* v_as_74_, size_t v_i_75_, size_t v_stop_76_){
_start:
{
uint8_t v___x_77_; 
v___x_77_ = lean_usize_dec_eq(v_i_75_, v_stop_76_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; uint8_t v___x_79_; uint8_t v___x_80_; uint8_t v___x_81_; uint8_t v___x_82_; 
v___x_78_ = lean_array_uget_borrowed(v_as_74_, v_i_75_);
v___x_79_ = 0;
v___x_80_ = lean_unbox(v___x_78_);
v___x_81_ = l_Lean_Meta_instBEqCongrArgKind_beq(v___x_80_, v___x_79_);
v___x_82_ = lean_bool_not(v___x_81_);
if (v___x_82_ == 0)
{
size_t v___x_83_; size_t v___x_84_; 
v___x_83_ = ((size_t)1ULL);
v___x_84_ = lean_usize_add(v_i_75_, v___x_83_);
v_i_75_ = v___x_84_;
goto _start;
}
else
{
return v___x_82_;
}
}
else
{
uint8_t v___x_86_; 
v___x_86_ = 0;
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2___boxed(lean_object* v_as_87_, lean_object* v_i_88_, lean_object* v_stop_89_){
_start:
{
size_t v_i_boxed_90_; size_t v_stop_boxed_91_; uint8_t v_res_92_; lean_object* v_r_93_; 
v_i_boxed_90_ = lean_unbox_usize(v_i_88_);
lean_dec(v_i_88_);
v_stop_boxed_91_ = lean_unbox_usize(v_stop_89_);
lean_dec(v_stop_89_);
v_res_92_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2(v_as_87_, v_i_boxed_90_, v_stop_boxed_91_);
lean_dec_ref(v_as_87_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0(size_t v_sz_94_, size_t v_i_95_, lean_object* v_bs_96_){
_start:
{
uint8_t v___x_97_; 
v___x_97_ = lean_usize_dec_lt(v_i_95_, v_sz_94_);
if (v___x_97_ == 0)
{
return v_bs_96_;
}
else
{
lean_object* v_v_98_; lean_object* v___x_99_; lean_object* v_bs_x27_100_; uint8_t v___x_101_; uint8_t v___x_102_; uint8_t v___x_103_; size_t v___x_104_; size_t v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_v_98_ = lean_array_uget(v_bs_96_, v_i_95_);
v___x_99_ = lean_unsigned_to_nat(0u);
v_bs_x27_100_ = lean_array_uset(v_bs_96_, v_i_95_, v___x_99_);
v___x_101_ = 2;
v___x_102_ = lean_unbox(v_v_98_);
lean_dec(v_v_98_);
v___x_103_ = l_Lean_Meta_instBEqCongrArgKind_beq(v___x_102_, v___x_101_);
v___x_104_ = ((size_t)1ULL);
v___x_105_ = lean_usize_add(v_i_95_, v___x_104_);
v___x_106_ = lean_box(v___x_103_);
v___x_107_ = lean_array_uset(v_bs_x27_100_, v_i_95_, v___x_106_);
v_i_95_ = v___x_105_;
v_bs_96_ = v___x_107_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0___boxed(lean_object* v_sz_109_, lean_object* v_i_110_, lean_object* v_bs_111_){
_start:
{
size_t v_sz_boxed_112_; size_t v_i_boxed_113_; lean_object* v_res_114_; 
v_sz_boxed_112_ = lean_unbox_usize(v_sz_109_);
lean_dec(v_sz_109_);
v_i_boxed_113_ = lean_unbox_usize(v_i_110_);
lean_dec(v_i_110_);
v_res_114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0(v_sz_boxed_112_, v_i_boxed_113_, v_bs_111_);
return v_res_114_;
}
}
static uint8_t _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___closed__0(void){
_start:
{
uint8_t v___x_115_; uint8_t v___x_116_; 
v___x_115_ = 1;
v___x_116_ = lean_bool_not(v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3(uint8_t v_a_117_, lean_object* v_as_118_, size_t v_i_119_, size_t v_stop_120_){
_start:
{
uint8_t v___x_121_; 
v___x_121_ = lean_usize_dec_eq(v_i_119_, v_stop_120_);
if (v___x_121_ == 0)
{
uint8_t v___x_122_; uint8_t v___y_124_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_122_ = 1;
v___x_128_ = lean_array_uget_borrowed(v_as_118_, v_i_119_);
v___x_129_ = lean_unbox(v___x_128_);
switch(v___x_129_)
{
case 0:
{
uint8_t v___x_130_; 
v___x_130_ = lean_uint8_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___closed__0);
v___y_124_ = v___x_130_;
goto v___jp_123_;
}
case 2:
{
uint8_t v___x_131_; 
v___x_131_ = lean_uint8_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___closed__0);
v___y_124_ = v___x_131_;
goto v___jp_123_;
}
default: 
{
uint8_t v___x_132_; 
v___x_132_ = lean_bool_not(v_a_117_);
v___y_124_ = v___x_132_;
goto v___jp_123_;
}
}
v___jp_123_:
{
if (v___y_124_ == 0)
{
size_t v___x_125_; size_t v___x_126_; 
v___x_125_ = ((size_t)1ULL);
v___x_126_ = lean_usize_add(v_i_119_, v___x_125_);
v_i_119_ = v___x_126_;
goto _start;
}
else
{
return v___x_122_;
}
}
}
else
{
uint8_t v___x_133_; 
v___x_133_ = 0;
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___boxed(lean_object* v_a_134_, lean_object* v_as_135_, lean_object* v_i_136_, lean_object* v_stop_137_){
_start:
{
uint8_t v_a_7759__boxed_138_; size_t v_i_boxed_139_; size_t v_stop_boxed_140_; uint8_t v_res_141_; lean_object* v_r_142_; 
v_a_7759__boxed_138_ = lean_unbox(v_a_134_);
v_i_boxed_139_ = lean_unbox_usize(v_i_136_);
lean_dec(v_i_136_);
v_stop_boxed_140_ = lean_unbox_usize(v_stop_137_);
lean_dec(v_stop_137_);
v_res_141_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3(v_a_7759__boxed_138_, v_as_135_, v_i_boxed_139_, v_stop_boxed_140_);
lean_dec_ref(v_as_135_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1___redArg(lean_object* v_xs_143_, lean_object* v_ys_144_, lean_object* v_x_145_){
_start:
{
lean_object* v_zero_146_; uint8_t v_isZero_147_; 
v_zero_146_ = lean_unsigned_to_nat(0u);
v_isZero_147_ = lean_nat_dec_eq(v_x_145_, v_zero_146_);
if (v_isZero_147_ == 1)
{
lean_dec(v_x_145_);
return v_isZero_147_;
}
else
{
lean_object* v_one_148_; lean_object* v_n_149_; lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; uint8_t v___x_153_; uint8_t v___x_154_; 
v_one_148_ = lean_unsigned_to_nat(1u);
v_n_149_ = lean_nat_sub(v_x_145_, v_one_148_);
lean_dec(v_x_145_);
v___x_150_ = lean_array_fget_borrowed(v_xs_143_, v_n_149_);
v___x_151_ = lean_array_fget_borrowed(v_ys_144_, v_n_149_);
v___x_152_ = lean_unbox(v___x_150_);
v___x_153_ = lean_unbox(v___x_151_);
v___x_154_ = l_Lean_Meta_instBEqCongrArgKind_beq(v___x_152_, v___x_153_);
if (v___x_154_ == 0)
{
lean_dec(v_n_149_);
return v___x_154_;
}
else
{
v_x_145_ = v_n_149_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1___redArg___boxed(lean_object* v_xs_156_, lean_object* v_ys_157_, lean_object* v_x_158_){
_start:
{
uint8_t v_res_159_; lean_object* v_r_160_; 
v_res_159_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1___redArg(v_xs_156_, v_ys_157_, v_x_158_);
lean_dec_ref(v_ys_157_);
lean_dec_ref(v_xs_156_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(lean_object* v_f_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v___x_167_; 
lean_inc_ref(v_f_161_);
v___x_167_ = l_Lean_Meta_isProof(v_f_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_311_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_311_ == 0)
{
v___x_170_ = v___x_167_;
v_isShared_171_ = v_isSharedCheck_311_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_167_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_311_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
uint8_t v___x_172_; 
v___x_172_ = lean_unbox(v_a_168_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; lean_object* v___x_174_; 
lean_del_object(v___x_170_);
v___x_173_ = lean_box(0);
lean_inc_ref(v_f_161_);
v___x_174_ = l_Lean_Meta_getFunInfo(v_f_161_, v___x_173_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_176_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_a_175_);
lean_dec_ref_known(v___x_174_, 1);
lean_inc_ref(v_f_161_);
v___x_176_ = l_Lean_Meta_getCongrSimpKinds(v_f_161_, v_a_175_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_290_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_290_ == 0)
{
v___x_179_ = v___x_176_;
v_isShared_180_ = v_isSharedCheck_290_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_176_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_290_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
uint8_t v___x_181_; lean_object* v___y_183_; lean_object* v___y_184_; lean_object* v___y_185_; lean_object* v___y_186_; lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___y_219_; uint8_t v___y_239_; uint8_t v___x_280_; 
v___x_181_ = 1;
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_array_get_size(v_a_177_);
v___x_280_ = lean_nat_dec_lt(v___x_216_, v___x_217_);
if (v___x_280_ == 0)
{
uint8_t v___x_281_; uint8_t v___x_282_; 
v___x_281_ = lean_unbox(v_a_168_);
v___x_282_ = lean_bool_not(v___x_281_);
v___y_239_ = v___x_282_;
goto v___jp_238_;
}
else
{
if (v___x_280_ == 0)
{
uint8_t v___x_283_; uint8_t v___x_284_; 
v___x_283_ = lean_unbox(v_a_168_);
v___x_284_ = lean_bool_not(v___x_283_);
v___y_239_ = v___x_284_;
goto v___jp_238_;
}
else
{
size_t v___x_285_; size_t v___x_286_; uint8_t v___x_287_; uint8_t v___x_288_; uint8_t v___x_289_; 
v___x_285_ = ((size_t)0ULL);
v___x_286_ = lean_usize_of_nat(v___x_217_);
v___x_287_ = lean_unbox(v_a_168_);
v___x_288_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3(v___x_287_, v_a_177_, v___x_285_, v___x_286_);
v___x_289_ = lean_bool_not(v___x_288_);
v___y_239_ = v___x_289_;
goto v___jp_238_;
}
}
v___jp_182_:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_Meta_mkCongrSimpCore_x3f(v_f_161_, v_a_175_, v_a_177_, v___x_181_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_207_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_207_ == 0)
{
v___x_190_ = v___x_187_;
v_isShared_191_ = v_isSharedCheck_207_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_187_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_207_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
if (lean_obj_tag(v_a_188_) == 1)
{
lean_object* v_val_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_202_; 
v_val_192_ = lean_ctor_get(v_a_188_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v_a_188_);
if (v_isSharedCheck_202_ == 0)
{
v___x_194_ = v_a_188_;
v_isShared_195_ = v_isSharedCheck_202_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_val_192_);
lean_dec(v_a_188_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_202_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
lean_ctor_set_tag(v___x_194_, 3);
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_val_192_);
v___x_197_ = v_reuseFailAlloc_201_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_199_; 
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_197_);
v___x_199_ = v___x_190_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_197_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
else
{
lean_object* v___x_203_; lean_object* v___x_205_; 
lean_dec(v_a_188_);
v___x_203_ = lean_box(0);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_203_);
v___x_205_ = v___x_190_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
else
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
v_a_208_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v___x_187_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_187_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
v___jp_218_:
{
if (v___y_219_ == 0)
{
lean_object* v___x_220_; 
v___x_220_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f(v_a_177_);
if (lean_obj_tag(v___x_220_) == 1)
{
lean_object* v_val_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
lean_dec(v_a_177_);
v_val_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_val_221_);
lean_dec_ref_known(v___x_220_, 1);
v___x_222_ = lean_nat_sub(v___x_217_, v_val_221_);
v___x_223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_223_, 0, v_val_221_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_223_);
v___x_225_ = v___x_179_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
else
{
size_t v_sz_227_; size_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_232_; 
lean_dec(v___x_220_);
v_sz_227_ = lean_array_size(v_a_177_);
v___x_228_ = ((size_t)0ULL);
v___x_229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0(v_sz_227_, v___x_228_, v_a_177_);
v___x_230_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_230_);
v___x_232_ = v___x_179_;
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
else
{
lean_object* v___x_234_; lean_object* v___x_236_; 
lean_dec(v_a_177_);
v___x_234_ = lean_box(0);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_234_);
v___x_236_ = v___x_179_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
v___jp_238_:
{
if (v___y_239_ == 0)
{
lean_del_object(v___x_179_);
lean_dec(v_a_168_);
if (lean_obj_tag(v_f_161_) == 4)
{
lean_object* v_declName_240_; lean_object* v_us_241_; lean_object* v___x_242_; 
v_declName_240_ = lean_ctor_get(v_f_161_, 0);
v_us_241_ = lean_ctor_get(v_f_161_, 1);
lean_inc(v_us_241_);
lean_inc(v_declName_240_);
v___x_242_ = l_Lean_Meta_mkCongrSimpForConst_x3f(v_declName_240_, v_us_241_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_262_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_262_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_262_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_262_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
if (lean_obj_tag(v_a_243_) == 1)
{
lean_object* v_val_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_261_; 
v_val_247_ = lean_ctor_get(v_a_243_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v_a_243_);
if (v_isSharedCheck_261_ == 0)
{
v___x_249_ = v_a_243_;
v_isShared_250_ = v_isSharedCheck_261_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_val_247_);
lean_dec(v_a_243_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_261_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v_argKinds_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v_argKinds_251_ = lean_ctor_get(v_val_247_, 2);
v___x_252_ = lean_array_get_size(v_argKinds_251_);
v___x_253_ = lean_nat_dec_eq(v___x_252_, v___x_217_);
if (v___x_253_ == 0)
{
lean_del_object(v___x_249_);
lean_dec(v_val_247_);
lean_del_object(v___x_245_);
v___y_183_ = v_a_162_;
v___y_184_ = v_a_163_;
v___y_185_ = v_a_164_;
v___y_186_ = v_a_165_;
goto v___jp_182_;
}
else
{
uint8_t v___x_254_; 
v___x_254_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1___redArg(v_argKinds_251_, v_a_177_, v___x_252_);
if (v___x_254_ == 0)
{
lean_del_object(v___x_249_);
lean_dec(v_val_247_);
lean_del_object(v___x_245_);
v___y_183_ = v_a_162_;
v___y_184_ = v_a_163_;
v___y_185_ = v_a_164_;
v___y_186_ = v_a_165_;
goto v___jp_182_;
}
else
{
lean_object* v___x_256_; 
lean_dec_ref_known(v_f_161_, 2);
lean_dec(v_a_177_);
lean_dec(v_a_175_);
if (v_isShared_250_ == 0)
{
lean_ctor_set_tag(v___x_249_, 3);
v___x_256_ = v___x_249_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_val_247_);
v___x_256_ = v_reuseFailAlloc_260_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_258_; 
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_256_);
v___x_258_ = v___x_245_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_245_);
lean_dec(v_a_243_);
v___y_183_ = v_a_162_;
v___y_184_ = v_a_163_;
v___y_185_ = v_a_164_;
v___y_186_ = v_a_165_;
goto v___jp_182_;
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
lean_dec_ref_known(v_f_161_, 2);
lean_dec(v_a_177_);
lean_dec(v_a_175_);
v_a_263_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_242_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_242_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
else
{
v___y_183_ = v_a_162_;
v___y_184_ = v_a_163_;
v___y_185_ = v_a_164_;
v___y_186_ = v_a_165_;
goto v___jp_182_;
}
}
else
{
uint8_t v___x_271_; 
lean_dec(v_a_175_);
lean_dec_ref(v_f_161_);
v___x_271_ = lean_nat_dec_lt(v___x_216_, v___x_217_);
if (v___x_271_ == 0)
{
uint8_t v___x_272_; uint8_t v___x_273_; 
v___x_272_ = lean_unbox(v_a_168_);
lean_dec(v_a_168_);
v___x_273_ = lean_bool_not(v___x_272_);
v___y_219_ = v___x_273_;
goto v___jp_218_;
}
else
{
if (v___x_271_ == 0)
{
uint8_t v___x_274_; uint8_t v___x_275_; 
v___x_274_ = lean_unbox(v_a_168_);
lean_dec(v_a_168_);
v___x_275_ = lean_bool_not(v___x_274_);
v___y_219_ = v___x_275_;
goto v___jp_218_;
}
else
{
size_t v___x_276_; size_t v___x_277_; uint8_t v___x_278_; uint8_t v___x_279_; 
lean_dec(v_a_168_);
v___x_276_ = ((size_t)0ULL);
v___x_277_ = lean_usize_of_nat(v___x_217_);
v___x_278_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2(v_a_177_, v___x_276_, v___x_277_);
v___x_279_ = lean_bool_not(v___x_278_);
v___y_219_ = v___x_279_;
goto v___jp_218_;
}
}
}
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec(v_a_175_);
lean_dec(v_a_168_);
lean_dec_ref(v_f_161_);
v_a_291_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_176_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_176_);
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
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_dec(v_a_168_);
lean_dec_ref(v_f_161_);
v_a_299_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_174_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_174_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
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
lean_object* v___x_307_; lean_object* v___x_309_; 
lean_dec(v_a_168_);
lean_dec_ref(v_f_161_);
v___x_307_ = lean_box(0);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_307_);
v___x_309_ = v___x_170_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
lean_dec_ref(v_f_161_);
v_a_312_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_167_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_167_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg___boxed(lean_object* v_f_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(v_f_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo(lean_object* v_f_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(v_f_327_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___boxed(lean_object* v_f_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo(v_f_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
return v_res_344_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1(lean_object* v_xs_345_, lean_object* v_ys_346_, lean_object* v_hsz_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
uint8_t v___x_350_; 
v___x_350_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1___redArg(v_xs_345_, v_ys_346_, v_x_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1___boxed(lean_object* v_xs_351_, lean_object* v_ys_352_, lean_object* v_hsz_353_, lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
uint8_t v_res_356_; lean_object* v_r_357_; 
v_res_356_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1(v_xs_351_, v_ys_352_, v_hsz_353_, v_x_354_, v_x_355_);
lean_dec_ref(v_ys_352_);
lean_dec_ref(v_xs_351_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_358_, lean_object* v_x_359_, lean_object* v_x_360_, lean_object* v_x_361_){
_start:
{
lean_object* v_ks_362_; lean_object* v_vs_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_387_; 
v_ks_362_ = lean_ctor_get(v_x_358_, 0);
v_vs_363_ = lean_ctor_get(v_x_358_, 1);
v_isSharedCheck_387_ = !lean_is_exclusive(v_x_358_);
if (v_isSharedCheck_387_ == 0)
{
v___x_365_ = v_x_358_;
v_isShared_366_ = v_isSharedCheck_387_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_vs_363_);
lean_inc(v_ks_362_);
lean_dec(v_x_358_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_387_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_367_ = lean_array_get_size(v_ks_362_);
v___x_368_ = lean_nat_dec_lt(v_x_359_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_372_; 
lean_dec(v_x_359_);
v___x_369_ = lean_array_push(v_ks_362_, v_x_360_);
v___x_370_ = lean_array_push(v_vs_363_, v_x_361_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 1, v___x_370_);
lean_ctor_set(v___x_365_, 0, v___x_369_);
v___x_372_ = v___x_365_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
else
{
lean_object* v_k_x27_374_; uint8_t v___x_375_; 
v_k_x27_374_ = lean_array_fget_borrowed(v_ks_362_, v_x_359_);
v___x_375_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_360_, v_k_x27_374_);
if (v___x_375_ == 0)
{
lean_object* v___x_377_; 
if (v_isShared_366_ == 0)
{
v___x_377_ = v___x_365_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_ks_362_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_vs_363_);
v___x_377_ = v_reuseFailAlloc_381_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_unsigned_to_nat(1u);
v___x_379_ = lean_nat_add(v_x_359_, v___x_378_);
lean_dec(v_x_359_);
v_x_358_ = v___x_377_;
v_x_359_ = v___x_379_;
goto _start;
}
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_382_ = lean_array_fset(v_ks_362_, v_x_359_, v_x_360_);
v___x_383_ = lean_array_fset(v_vs_363_, v_x_359_, v_x_361_);
lean_dec(v_x_359_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 1, v___x_383_);
lean_ctor_set(v___x_365_, 0, v___x_382_);
v___x_385_ = v___x_365_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_382_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4___redArg(lean_object* v_n_388_, lean_object* v_k_389_, lean_object* v_v_390_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5___redArg(v_n_388_, v___x_391_, v_k_389_, v_v_390_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(lean_object* v_x_394_, size_t v_x_395_, size_t v_x_396_, lean_object* v_x_397_, lean_object* v_x_398_){
_start:
{
if (lean_obj_tag(v_x_394_) == 0)
{
lean_object* v_es_399_; size_t v___x_400_; size_t v___x_401_; lean_object* v_j_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v_es_399_ = lean_ctor_get(v_x_394_, 0);
v___x_400_ = ((size_t)31ULL);
v___x_401_ = lean_usize_land(v_x_395_, v___x_400_);
v_j_402_ = lean_usize_to_nat(v___x_401_);
v___x_403_ = lean_array_get_size(v_es_399_);
v___x_404_ = lean_nat_dec_lt(v_j_402_, v___x_403_);
if (v___x_404_ == 0)
{
lean_dec(v_j_402_);
lean_dec(v_x_398_);
lean_dec_ref(v_x_397_);
return v_x_394_;
}
else
{
lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_443_; 
lean_inc_ref(v_es_399_);
v_isSharedCheck_443_ = !lean_is_exclusive(v_x_394_);
if (v_isSharedCheck_443_ == 0)
{
lean_object* v_unused_444_; 
v_unused_444_ = lean_ctor_get(v_x_394_, 0);
lean_dec(v_unused_444_);
v___x_406_ = v_x_394_;
v_isShared_407_ = v_isSharedCheck_443_;
goto v_resetjp_405_;
}
else
{
lean_dec(v_x_394_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_443_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v_v_408_; lean_object* v___x_409_; lean_object* v_xs_x27_410_; lean_object* v___y_412_; 
v_v_408_ = lean_array_fget(v_es_399_, v_j_402_);
v___x_409_ = lean_box(0);
v_xs_x27_410_ = lean_array_fset(v_es_399_, v_j_402_, v___x_409_);
switch(lean_obj_tag(v_v_408_))
{
case 0:
{
lean_object* v_key_417_; lean_object* v_val_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_428_; 
v_key_417_ = lean_ctor_get(v_v_408_, 0);
v_val_418_ = lean_ctor_get(v_v_408_, 1);
v_isSharedCheck_428_ = !lean_is_exclusive(v_v_408_);
if (v_isSharedCheck_428_ == 0)
{
v___x_420_ = v_v_408_;
v_isShared_421_ = v_isSharedCheck_428_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_val_418_);
lean_inc(v_key_417_);
lean_dec(v_v_408_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_428_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
uint8_t v___x_422_; 
v___x_422_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_397_, v_key_417_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; 
lean_del_object(v___x_420_);
v___x_423_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_417_, v_val_418_, v_x_397_, v_x_398_);
v___x_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
v___y_412_ = v___x_424_;
goto v___jp_411_;
}
else
{
lean_object* v___x_426_; 
lean_dec(v_val_418_);
lean_dec(v_key_417_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 1, v_x_398_);
lean_ctor_set(v___x_420_, 0, v_x_397_);
v___x_426_ = v___x_420_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_x_397_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_x_398_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
v___y_412_ = v___x_426_;
goto v___jp_411_;
}
}
}
}
case 1:
{
lean_object* v_node_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_441_; 
v_node_429_ = lean_ctor_get(v_v_408_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v_v_408_);
if (v_isSharedCheck_441_ == 0)
{
v___x_431_ = v_v_408_;
v_isShared_432_ = v_isSharedCheck_441_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_node_429_);
lean_dec(v_v_408_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_441_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
size_t v___x_433_; size_t v___x_434_; size_t v___x_435_; size_t v___x_436_; lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_433_ = ((size_t)5ULL);
v___x_434_ = lean_usize_shift_right(v_x_395_, v___x_433_);
v___x_435_ = ((size_t)1ULL);
v___x_436_ = lean_usize_add(v_x_396_, v___x_435_);
v___x_437_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_node_429_, v___x_434_, v___x_436_, v_x_397_, v_x_398_);
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
v___y_412_ = v___x_439_;
goto v___jp_411_;
}
}
}
default: 
{
lean_object* v___x_442_; 
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v_x_397_);
lean_ctor_set(v___x_442_, 1, v_x_398_);
v___y_412_ = v___x_442_;
goto v___jp_411_;
}
}
v___jp_411_:
{
lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_413_ = lean_array_fset(v_xs_x27_410_, v_j_402_, v___y_412_);
lean_dec(v_j_402_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v___x_413_);
v___x_415_ = v___x_406_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
else
{
lean_object* v_ks_445_; lean_object* v_vs_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_466_; 
v_ks_445_ = lean_ctor_get(v_x_394_, 0);
v_vs_446_ = lean_ctor_get(v_x_394_, 1);
v_isSharedCheck_466_ = !lean_is_exclusive(v_x_394_);
if (v_isSharedCheck_466_ == 0)
{
v___x_448_ = v_x_394_;
v_isShared_449_ = v_isSharedCheck_466_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_vs_446_);
lean_inc(v_ks_445_);
lean_dec(v_x_394_);
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
v_newNode_452_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4___redArg(v___x_451_, v_x_397_, v_x_398_);
v___x_460_ = ((size_t)7ULL);
v___x_461_ = lean_usize_dec_le(v___x_460_, v_x_396_);
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
v___x_459_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(v_x_396_, v_ks_455_, v_vs_456_, v___x_457_, v___x_458_);
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
lean_object* v_k_474_; lean_object* v_v_475_; uint64_t v___x_476_; size_t v_h_477_; size_t v___x_478_; lean_object* v___x_479_; size_t v___x_480_; size_t v___x_481_; size_t v___x_482_; size_t v_h_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_k_474_ = lean_array_fget_borrowed(v_keys_468_, v_i_470_);
v_v_475_ = lean_array_fget_borrowed(v_vals_469_, v_i_470_);
v___x_476_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_474_);
v_h_477_ = lean_uint64_to_usize(v___x_476_);
v___x_478_ = ((size_t)5ULL);
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_480_ = ((size_t)1ULL);
v___x_481_ = lean_usize_sub(v_depth_467_, v___x_480_);
v___x_482_ = lean_usize_mul(v___x_478_, v___x_481_);
v_h_483_ = lean_usize_shift_right(v_h_477_, v___x_482_);
v___x_484_ = lean_nat_add(v_i_470_, v___x_479_);
lean_dec(v_i_470_);
lean_inc(v_v_475_);
lean_inc(v_k_474_);
v___x_485_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_entries_471_, v_h_483_, v_depth_467_, v_k_474_, v_v_475_);
v_i_470_ = v___x_484_;
v_entries_471_ = v___x_485_;
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
size_t v_x_2447__boxed_499_; size_t v_x_2448__boxed_500_; lean_object* v_res_501_; 
v_x_2447__boxed_499_ = lean_unbox_usize(v_x_495_);
lean_dec(v_x_495_);
v_x_2448__boxed_500_ = lean_unbox_usize(v_x_496_);
lean_dec(v_x_496_);
v_res_501_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_x_494_, v_x_2447__boxed_499_, v_x_2448__boxed_500_, v_x_497_, v_x_498_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1___redArg(lean_object* v_x_502_, lean_object* v_x_503_, lean_object* v_x_504_){
_start:
{
uint64_t v___x_505_; size_t v___x_506_; size_t v___x_507_; lean_object* v___x_508_; 
v___x_505_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_503_);
v___x_506_ = lean_uint64_to_usize(v___x_505_);
v___x_507_ = ((size_t)1ULL);
v___x_508_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_x_502_, v___x_506_, v___x_507_, v_x_503_, v_x_504_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_509_, lean_object* v_vals_510_, lean_object* v_i_511_, lean_object* v_k_512_){
_start:
{
lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_513_ = lean_array_get_size(v_keys_509_);
v___x_514_ = lean_nat_dec_lt(v_i_511_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; 
lean_dec(v_i_511_);
v___x_515_ = lean_box(0);
return v___x_515_;
}
else
{
lean_object* v_k_x27_516_; uint8_t v___x_517_; 
v_k_x27_516_ = lean_array_fget_borrowed(v_keys_509_, v_i_511_);
v___x_517_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_512_, v_k_x27_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = lean_nat_add(v_i_511_, v___x_518_);
lean_dec(v_i_511_);
v_i_511_ = v___x_519_;
goto _start;
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_array_fget_borrowed(v_vals_510_, v_i_511_);
lean_dec(v_i_511_);
lean_inc(v___x_521_);
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_523_, lean_object* v_vals_524_, lean_object* v_i_525_, lean_object* v_k_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(v_keys_523_, v_vals_524_, v_i_525_, v_k_526_);
lean_dec_ref(v_k_526_);
lean_dec_ref(v_vals_524_);
lean_dec_ref(v_keys_523_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(lean_object* v_x_528_, size_t v_x_529_, lean_object* v_x_530_){
_start:
{
if (lean_obj_tag(v_x_528_) == 0)
{
lean_object* v_es_531_; lean_object* v___x_532_; size_t v___x_533_; size_t v___x_534_; lean_object* v_j_535_; lean_object* v___x_536_; 
v_es_531_ = lean_ctor_get(v_x_528_, 0);
v___x_532_ = lean_box(2);
v___x_533_ = ((size_t)31ULL);
v___x_534_ = lean_usize_land(v_x_529_, v___x_533_);
v_j_535_ = lean_usize_to_nat(v___x_534_);
v___x_536_ = lean_array_get_borrowed(v___x_532_, v_es_531_, v_j_535_);
lean_dec(v_j_535_);
switch(lean_obj_tag(v___x_536_))
{
case 0:
{
lean_object* v_key_537_; lean_object* v_val_538_; uint8_t v___x_539_; 
v_key_537_ = lean_ctor_get(v___x_536_, 0);
v_val_538_ = lean_ctor_get(v___x_536_, 1);
v___x_539_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_530_, v_key_537_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; 
v___x_540_ = lean_box(0);
return v___x_540_;
}
else
{
lean_object* v___x_541_; 
lean_inc(v_val_538_);
v___x_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_541_, 0, v_val_538_);
return v___x_541_;
}
}
case 1:
{
lean_object* v_node_542_; size_t v___x_543_; size_t v___x_544_; 
v_node_542_ = lean_ctor_get(v___x_536_, 0);
v___x_543_ = ((size_t)5ULL);
v___x_544_ = lean_usize_shift_right(v_x_529_, v___x_543_);
v_x_528_ = v_node_542_;
v_x_529_ = v___x_544_;
goto _start;
}
default: 
{
lean_object* v___x_546_; 
v___x_546_ = lean_box(0);
return v___x_546_;
}
}
}
else
{
lean_object* v_ks_547_; lean_object* v_vs_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v_ks_547_ = lean_ctor_get(v_x_528_, 0);
v_vs_548_ = lean_ctor_get(v_x_528_, 1);
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(v_ks_547_, v_vs_548_, v___x_549_, v_x_530_);
return v___x_550_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg___boxed(lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
size_t v_x_2635__boxed_554_; lean_object* v_res_555_; 
v_x_2635__boxed_554_ = lean_unbox_usize(v_x_552_);
lean_dec(v_x_552_);
v_res_555_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(v_x_551_, v_x_2635__boxed_554_, v_x_553_);
lean_dec_ref(v_x_553_);
lean_dec_ref(v_x_551_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(lean_object* v_x_556_, lean_object* v_x_557_){
_start:
{
uint64_t v___x_558_; size_t v___x_559_; lean_object* v___x_560_; 
v___x_558_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_557_);
v___x_559_ = lean_uint64_to_usize(v___x_558_);
v___x_560_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(v_x_556_, v___x_559_, v_x_557_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg___boxed(lean_object* v_x_561_, lean_object* v_x_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(v_x_561_, v_x_562_);
lean_dec_ref(v_x_562_);
lean_dec_ref(v_x_561_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCongrInfo___redArg(lean_object* v_f_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___x_571_; lean_object* v_congrInfo_572_; lean_object* v___x_573_; 
v___x_571_ = lean_st_ref_get(v_a_565_);
v_congrInfo_572_ = lean_ctor_get(v___x_571_, 5);
lean_inc_ref(v_congrInfo_572_);
lean_dec(v___x_571_);
v___x_573_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(v_congrInfo_572_, v_f_564_);
lean_dec_ref(v_congrInfo_572_);
if (lean_obj_tag(v___x_573_) == 1)
{
lean_object* v_val_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
lean_dec_ref(v_f_564_);
v_val_574_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_573_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_val_574_);
lean_dec(v___x_573_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
lean_ctor_set_tag(v___x_576_, 0);
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_val_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
else
{
lean_object* v___x_582_; 
lean_dec(v___x_573_);
lean_inc_ref(v_f_564_);
v___x_582_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(v_f_564_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_612_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_612_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_612_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_612_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v_share_588_; lean_object* v_maxFVar_589_; lean_object* v_proofInstInfo_590_; lean_object* v_inferType_591_; lean_object* v_getLevel_592_; lean_object* v_congrInfo_593_; lean_object* v_defEqI_594_; lean_object* v_extensions_595_; lean_object* v_issues_596_; lean_object* v_canon_597_; lean_object* v_instanceOverrides_598_; uint8_t v_debug_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_611_; 
v___x_587_ = lean_st_ref_take(v_a_565_);
v_share_588_ = lean_ctor_get(v___x_587_, 0);
v_maxFVar_589_ = lean_ctor_get(v___x_587_, 1);
v_proofInstInfo_590_ = lean_ctor_get(v___x_587_, 2);
v_inferType_591_ = lean_ctor_get(v___x_587_, 3);
v_getLevel_592_ = lean_ctor_get(v___x_587_, 4);
v_congrInfo_593_ = lean_ctor_get(v___x_587_, 5);
v_defEqI_594_ = lean_ctor_get(v___x_587_, 6);
v_extensions_595_ = lean_ctor_get(v___x_587_, 7);
v_issues_596_ = lean_ctor_get(v___x_587_, 8);
v_canon_597_ = lean_ctor_get(v___x_587_, 9);
v_instanceOverrides_598_ = lean_ctor_get(v___x_587_, 10);
v_debug_599_ = lean_ctor_get_uint8(v___x_587_, sizeof(void*)*11);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_611_ == 0)
{
v___x_601_ = v___x_587_;
v_isShared_602_ = v_isSharedCheck_611_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_instanceOverrides_598_);
lean_inc(v_canon_597_);
lean_inc(v_issues_596_);
lean_inc(v_extensions_595_);
lean_inc(v_defEqI_594_);
lean_inc(v_congrInfo_593_);
lean_inc(v_getLevel_592_);
lean_inc(v_inferType_591_);
lean_inc(v_proofInstInfo_590_);
lean_inc(v_maxFVar_589_);
lean_inc(v_share_588_);
lean_dec(v___x_587_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_611_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; lean_object* v___x_605_; 
lean_inc(v_a_583_);
v___x_603_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1___redArg(v_congrInfo_593_, v_f_564_, v_a_583_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 5, v___x_603_);
v___x_605_ = v___x_601_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_share_588_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_maxFVar_589_);
lean_ctor_set(v_reuseFailAlloc_610_, 2, v_proofInstInfo_590_);
lean_ctor_set(v_reuseFailAlloc_610_, 3, v_inferType_591_);
lean_ctor_set(v_reuseFailAlloc_610_, 4, v_getLevel_592_);
lean_ctor_set(v_reuseFailAlloc_610_, 5, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_610_, 6, v_defEqI_594_);
lean_ctor_set(v_reuseFailAlloc_610_, 7, v_extensions_595_);
lean_ctor_set(v_reuseFailAlloc_610_, 8, v_issues_596_);
lean_ctor_set(v_reuseFailAlloc_610_, 9, v_canon_597_);
lean_ctor_set(v_reuseFailAlloc_610_, 10, v_instanceOverrides_598_);
lean_ctor_set_uint8(v_reuseFailAlloc_610_, sizeof(void*)*11, v_debug_599_);
v___x_605_ = v_reuseFailAlloc_610_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_606_ = lean_st_ref_set(v_a_565_, v___x_605_);
if (v_isShared_586_ == 0)
{
v___x_608_ = v___x_585_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_583_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_564_);
return v___x_582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCongrInfo___redArg___boxed(lean_object* v_f_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_Meta_Sym_getCongrInfo___redArg(v_f_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_);
lean_dec(v_a_618_);
lean_dec_ref(v_a_617_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
lean_dec(v_a_614_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCongrInfo(lean_object* v_f_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_Meta_Sym_getCongrInfo___redArg(v_f_621_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCongrInfo___boxed(lean_object* v_f_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_Meta_Sym_getCongrInfo(v_f_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0(lean_object* v_00_u03b2_639_, lean_object* v_x_640_, lean_object* v_x_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(v_x_640_, v_x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___boxed(lean_object* v_00_u03b2_643_, lean_object* v_x_644_, lean_object* v_x_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0(v_00_u03b2_643_, v_x_644_, v_x_645_);
lean_dec_ref(v_x_645_);
lean_dec_ref(v_x_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1(lean_object* v_00_u03b2_647_, lean_object* v_x_648_, lean_object* v_x_649_, lean_object* v_x_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1___redArg(v_x_648_, v_x_649_, v_x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0(lean_object* v_00_u03b2_652_, lean_object* v_x_653_, size_t v_x_654_, lean_object* v_x_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(v_x_653_, v_x_654_, v_x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___boxed(lean_object* v_00_u03b2_657_, lean_object* v_x_658_, lean_object* v_x_659_, lean_object* v_x_660_){
_start:
{
size_t v_x_2777__boxed_661_; lean_object* v_res_662_; 
v_x_2777__boxed_661_ = lean_unbox_usize(v_x_659_);
lean_dec(v_x_659_);
v_res_662_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0(v_00_u03b2_657_, v_x_658_, v_x_2777__boxed_661_, v_x_660_);
lean_dec_ref(v_x_660_);
lean_dec_ref(v_x_658_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2(lean_object* v_00_u03b2_663_, lean_object* v_x_664_, size_t v_x_665_, size_t v_x_666_, lean_object* v_x_667_, lean_object* v_x_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_x_664_, v_x_665_, v_x_666_, v_x_667_, v_x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___boxed(lean_object* v_00_u03b2_670_, lean_object* v_x_671_, lean_object* v_x_672_, lean_object* v_x_673_, lean_object* v_x_674_, lean_object* v_x_675_){
_start:
{
size_t v_x_2788__boxed_676_; size_t v_x_2789__boxed_677_; lean_object* v_res_678_; 
v_x_2788__boxed_676_ = lean_unbox_usize(v_x_672_);
lean_dec(v_x_672_);
v_x_2789__boxed_677_ = lean_unbox_usize(v_x_673_);
lean_dec(v_x_673_);
v_res_678_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2(v_00_u03b2_670_, v_x_671_, v_x_2788__boxed_676_, v_x_2789__boxed_677_, v_x_674_, v_x_675_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_679_, lean_object* v_keys_680_, lean_object* v_vals_681_, lean_object* v_heq_682_, lean_object* v_i_683_, lean_object* v_k_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(v_keys_680_, v_vals_681_, v_i_683_, v_k_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_686_, lean_object* v_keys_687_, lean_object* v_vals_688_, lean_object* v_heq_689_, lean_object* v_i_690_, lean_object* v_k_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1(v_00_u03b2_686_, v_keys_687_, v_vals_688_, v_heq_689_, v_i_690_, v_k_691_);
lean_dec_ref(v_k_691_);
lean_dec_ref(v_vals_688_);
lean_dec_ref(v_keys_687_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_693_, lean_object* v_n_694_, lean_object* v_k_695_, lean_object* v_v_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4___redArg(v_n_694_, v_k_695_, v_v_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_698_, size_t v_depth_699_, lean_object* v_keys_700_, lean_object* v_vals_701_, lean_object* v_heq_702_, lean_object* v_i_703_, lean_object* v_entries_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(v_depth_699_, v_keys_700_, v_vals_701_, v_i_703_, v_entries_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_706_, lean_object* v_depth_707_, lean_object* v_keys_708_, lean_object* v_vals_709_, lean_object* v_heq_710_, lean_object* v_i_711_, lean_object* v_entries_712_){
_start:
{
size_t v_depth_boxed_713_; lean_object* v_res_714_; 
v_depth_boxed_713_ = lean_unbox_usize(v_depth_707_);
lean_dec(v_depth_707_);
v_res_714_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5(v_00_u03b2_706_, v_depth_boxed_713_, v_keys_708_, v_vals_709_, v_heq_710_, v_i_711_, v_entries_712_);
lean_dec_ref(v_vals_709_);
lean_dec_ref(v_keys_708_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_715_, lean_object* v_x_716_, lean_object* v_x_717_, lean_object* v_x_718_, lean_object* v_x_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5___redArg(v_x_716_, v_x_717_, v_x_718_, v_x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0(lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
if (lean_obj_tag(v_a_723_) == 0)
{
lean_object* v___x_725_; 
v___x_725_ = l_List_reverse___redArg(v_a_724_);
return v___x_725_;
}
else
{
lean_object* v_head_726_; lean_object* v_tail_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_742_; 
v_head_726_ = lean_ctor_get(v_a_723_, 0);
v_tail_727_ = lean_ctor_get(v_a_723_, 1);
v_isSharedCheck_742_ = !lean_is_exclusive(v_a_723_);
if (v_isSharedCheck_742_ == 0)
{
v___x_729_ = v_a_723_;
v_isShared_730_ = v_isSharedCheck_742_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_tail_727_);
lean_inc(v_head_726_);
lean_dec(v_a_723_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_742_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___y_732_; uint8_t v___x_739_; 
v___x_739_ = lean_unbox(v_head_726_);
lean_dec(v_head_726_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
v___x_740_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__0));
v___y_732_ = v___x_740_;
goto v___jp_731_;
}
else
{
lean_object* v___x_741_; 
v___x_741_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__1));
v___y_732_ = v___x_741_;
goto v___jp_731_;
}
v___jp_731_:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
lean_inc_ref(v___y_732_);
v___x_733_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_733_, 0, v___y_732_);
v___x_734_ = l_Lean_MessageData_ofFormat(v___x_733_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v_a_724_);
lean_ctor_set(v___x_729_, 0, v___x_734_);
v___x_736_ = v___x_729_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_a_724_);
v___x_736_ = v_reuseFailAlloc_738_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
v_a_723_ = v_tail_727_;
v_a_724_ = v___x_736_;
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
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__1));
v___x_747_ = l_Lean_MessageData_ofFormat(v___x_746_);
return v___x_747_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__3));
v___x_750_ = l_Lean_stringToMessageData(v___x_749_);
return v___x_750_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__5));
v___x_753_ = l_Lean_stringToMessageData(v___x_752_);
return v___x_753_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__7));
v___x_756_ = l_Lean_stringToMessageData(v___x_755_);
return v___x_756_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__9));
v___x_759_ = l_Lean_stringToMessageData(v___x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData(lean_object* v_x_760_){
_start:
{
switch(lean_obj_tag(v_x_760_))
{
case 0:
{
lean_object* v___x_761_; 
v___x_761_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2);
return v___x_761_;
}
case 1:
{
lean_object* v_prefixSize_762_; lean_object* v_suffixSize_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_780_; 
v_prefixSize_762_ = lean_ctor_get(v_x_760_, 0);
v_suffixSize_763_ = lean_ctor_get(v_x_760_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v_x_760_);
if (v_isSharedCheck_780_ == 0)
{
v___x_765_ = v_x_760_;
v_isShared_766_ = v_isSharedCheck_780_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_suffixSize_763_);
lean_inc(v_prefixSize_762_);
lean_dec(v_x_760_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_780_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_767_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4);
v___x_768_ = l_Nat_reprFast(v_prefixSize_762_);
v___x_769_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
v___x_770_ = l_Lean_MessageData_ofFormat(v___x_769_);
if (v_isShared_766_ == 0)
{
lean_ctor_set_tag(v___x_765_, 7);
lean_ctor_set(v___x_765_, 1, v___x_770_);
lean_ctor_set(v___x_765_, 0, v___x_767_);
v___x_772_ = v___x_765_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_770_);
v___x_772_ = v_reuseFailAlloc_779_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_773_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6);
v___x_774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_772_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = l_Nat_reprFast(v_suffixSize_763_);
v___x_776_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
v___x_777_ = l_Lean_MessageData_ofFormat(v___x_776_);
v___x_778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_774_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
return v___x_778_;
}
}
}
case 2:
{
lean_object* v_rewritable_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_rewritable_781_ = lean_ctor_get(v_x_760_, 0);
lean_inc_ref(v_rewritable_781_);
lean_dec_ref_known(v_x_760_, 1);
v___x_782_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8);
v___x_783_ = lean_array_to_list(v_rewritable_781_);
v___x_784_ = lean_box(0);
v___x_785_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0(v___x_783_, v___x_784_);
v___x_786_ = l_Lean_MessageData_ofList(v___x_785_);
v___x_787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_782_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
return v___x_787_;
}
default: 
{
lean_object* v_thm_788_; lean_object* v_proof_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_thm_788_ = lean_ctor_get(v_x_760_, 0);
lean_inc_ref(v_thm_788_);
lean_dec_ref_known(v_x_760_, 1);
v_proof_789_ = lean_ctor_get(v_thm_788_, 1);
lean_inc_ref(v_proof_789_);
lean_dec_ref(v_thm_788_);
v___x_790_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10);
v___x_791_ = l_Lean_MessageData_ofExpr(v_proof_789_);
v___x_792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_790_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
return v___x_792_;
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
