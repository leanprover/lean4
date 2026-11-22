// Lean compiler output
// Module: Lean.Meta.Sym.Simp.CongrInfo
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.FunInfo import Lean.Util.CollectLooseBVars import Init.Omega
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
lean_object* l_Lean_Expr_getForallBody(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_getForallArity(lean_object*);
lean_object* l_Lean_Expr_looseBVarMask(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrTheoremInfo(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrTheoremInfo(lean_object* v_thm_73_){
_start:
{
lean_object* v_type_74_; lean_object* v___x_75_; lean_object* v_rhs_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v_type_74_ = lean_ctor_get(v_thm_73_, 0);
v___x_75_ = l_Lean_Expr_getForallBody(v_type_74_);
v_rhs_76_ = l_Lean_Expr_appArg_x21(v___x_75_);
lean_dec_ref(v___x_75_);
lean_inc_ref(v_type_74_);
v___x_77_ = l_Lean_Expr_getForallArity(v_type_74_);
v___x_78_ = l_Lean_Expr_looseBVarMask(v_rhs_76_, v___x_77_);
lean_dec(v___x_77_);
lean_dec_ref(v_rhs_76_);
v___x_79_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_79_, 0, v_thm_73_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg(lean_object* v_xs_80_, lean_object* v_ys_81_, lean_object* v_x_82_){
_start:
{
lean_object* v_zero_83_; uint8_t v_isZero_84_; 
v_zero_83_ = lean_unsigned_to_nat(0u);
v_isZero_84_ = lean_nat_dec_eq(v_x_82_, v_zero_83_);
if (v_isZero_84_ == 1)
{
lean_dec(v_x_82_);
return v_isZero_84_;
}
else
{
lean_object* v_one_85_; lean_object* v_n_86_; lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; uint8_t v___x_90_; uint8_t v___x_91_; 
v_one_85_ = lean_unsigned_to_nat(1u);
v_n_86_ = lean_nat_sub(v_x_82_, v_one_85_);
lean_dec(v_x_82_);
v___x_87_ = lean_array_fget_borrowed(v_xs_80_, v_n_86_);
v___x_88_ = lean_array_fget_borrowed(v_ys_81_, v_n_86_);
v___x_89_ = lean_unbox(v___x_87_);
v___x_90_ = lean_unbox(v___x_88_);
v___x_91_ = l_Lean_Meta_instBEqCongrArgKind_beq(v___x_89_, v___x_90_);
if (v___x_91_ == 0)
{
lean_dec(v_n_86_);
return v___x_91_;
}
else
{
v_x_82_ = v_n_86_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg___boxed(lean_object* v_xs_93_, lean_object* v_ys_94_, lean_object* v_x_95_){
_start:
{
uint8_t v_res_96_; lean_object* v_r_97_; 
v_res_96_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg(v_xs_93_, v_ys_94_, v_x_95_);
lean_dec_ref(v_ys_94_);
lean_dec_ref(v_xs_93_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0(uint8_t v___y_98_, uint8_t v_a_99_, lean_object* v_as_100_, size_t v_i_101_, size_t v_stop_102_){
_start:
{
uint8_t v___x_103_; 
v___x_103_ = lean_usize_dec_eq(v_i_101_, v_stop_102_);
if (v___x_103_ == 0)
{
uint8_t v___x_104_; uint8_t v___y_106_; lean_object* v___x_110_; uint8_t v___x_111_; uint8_t v___x_112_; uint8_t v___x_113_; 
v___x_104_ = 1;
v___x_110_ = lean_array_uget_borrowed(v_as_100_, v_i_101_);
v___x_111_ = 0;
v___x_112_ = lean_unbox(v___x_110_);
v___x_113_ = l_Lean_Meta_instBEqCongrArgKind_beq(v___x_112_, v___x_111_);
if (v___x_113_ == 0)
{
v___y_106_ = v___y_98_;
goto v___jp_105_;
}
else
{
v___y_106_ = v_a_99_;
goto v___jp_105_;
}
v___jp_105_:
{
if (v___y_106_ == 0)
{
size_t v___x_107_; size_t v___x_108_; 
v___x_107_ = ((size_t)1ULL);
v___x_108_ = lean_usize_add(v_i_101_, v___x_107_);
v_i_101_ = v___x_108_;
goto _start;
}
else
{
return v___x_104_;
}
}
}
else
{
uint8_t v___x_114_; 
v___x_114_ = 0;
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0___boxed(lean_object* v___y_115_, lean_object* v_a_116_, lean_object* v_as_117_, lean_object* v_i_118_, lean_object* v_stop_119_){
_start:
{
uint8_t v___y_6083__boxed_120_; uint8_t v_a_6084__boxed_121_; size_t v_i_boxed_122_; size_t v_stop_boxed_123_; uint8_t v_res_124_; lean_object* v_r_125_; 
v___y_6083__boxed_120_ = lean_unbox(v___y_115_);
v_a_6084__boxed_121_ = lean_unbox(v_a_116_);
v_i_boxed_122_ = lean_unbox_usize(v_i_118_);
lean_dec(v_i_118_);
v_stop_boxed_123_ = lean_unbox_usize(v_stop_119_);
lean_dec(v_stop_119_);
v_res_124_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0(v___y_6083__boxed_120_, v_a_6084__boxed_121_, v_as_117_, v_i_boxed_122_, v_stop_boxed_123_);
lean_dec_ref(v_as_117_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1(size_t v_sz_126_, size_t v_i_127_, lean_object* v_bs_128_){
_start:
{
uint8_t v___x_129_; 
v___x_129_ = lean_usize_dec_lt(v_i_127_, v_sz_126_);
if (v___x_129_ == 0)
{
return v_bs_128_;
}
else
{
lean_object* v_v_130_; lean_object* v___x_131_; lean_object* v_bs_x27_132_; uint8_t v___x_133_; uint8_t v___x_134_; uint8_t v___x_135_; size_t v___x_136_; size_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_v_130_ = lean_array_uget(v_bs_128_, v_i_127_);
v___x_131_ = lean_unsigned_to_nat(0u);
v_bs_x27_132_ = lean_array_uset(v_bs_128_, v_i_127_, v___x_131_);
v___x_133_ = 2;
v___x_134_ = lean_unbox(v_v_130_);
lean_dec(v_v_130_);
v___x_135_ = l_Lean_Meta_instBEqCongrArgKind_beq(v___x_134_, v___x_133_);
v___x_136_ = ((size_t)1ULL);
v___x_137_ = lean_usize_add(v_i_127_, v___x_136_);
v___x_138_ = lean_box(v___x_135_);
v___x_139_ = lean_array_uset(v_bs_x27_132_, v_i_127_, v___x_138_);
v_i_127_ = v___x_137_;
v_bs_128_ = v___x_139_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1___boxed(lean_object* v_sz_141_, lean_object* v_i_142_, lean_object* v_bs_143_){
_start:
{
size_t v_sz_boxed_144_; size_t v_i_boxed_145_; lean_object* v_res_146_; 
v_sz_boxed_144_ = lean_unbox_usize(v_sz_141_);
lean_dec(v_sz_141_);
v_i_boxed_145_ = lean_unbox_usize(v_i_142_);
lean_dec(v_i_142_);
v_res_146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1(v_sz_boxed_144_, v_i_boxed_145_, v_bs_143_);
return v_res_146_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2(uint8_t v_a_147_, lean_object* v_as_148_, size_t v_i_149_, size_t v_stop_150_){
_start:
{
uint8_t v___x_151_; 
v___x_151_ = lean_usize_dec_eq(v_i_149_, v_stop_150_);
if (v___x_151_ == 0)
{
uint8_t v___x_152_; uint8_t v___y_154_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_152_ = 1;
v___x_158_ = lean_array_uget_borrowed(v_as_148_, v_i_149_);
v___x_159_ = lean_unbox(v___x_158_);
switch(v___x_159_)
{
case 0:
{
v___y_154_ = v_a_147_;
goto v___jp_153_;
}
case 2:
{
v___y_154_ = v_a_147_;
goto v___jp_153_;
}
default: 
{
return v___x_152_;
}
}
v___jp_153_:
{
if (v___y_154_ == 0)
{
size_t v___x_155_; size_t v___x_156_; 
v___x_155_ = ((size_t)1ULL);
v___x_156_ = lean_usize_add(v_i_149_, v___x_155_);
v_i_149_ = v___x_156_;
goto _start;
}
else
{
return v___x_152_;
}
}
}
else
{
uint8_t v___x_160_; 
v___x_160_ = 0;
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2___boxed(lean_object* v_a_161_, lean_object* v_as_162_, lean_object* v_i_163_, lean_object* v_stop_164_){
_start:
{
uint8_t v_a_6133__boxed_165_; size_t v_i_boxed_166_; size_t v_stop_boxed_167_; uint8_t v_res_168_; lean_object* v_r_169_; 
v_a_6133__boxed_165_ = lean_unbox(v_a_161_);
v_i_boxed_166_ = lean_unbox_usize(v_i_163_);
lean_dec(v_i_163_);
v_stop_boxed_167_ = lean_unbox_usize(v_stop_164_);
lean_dec(v_stop_164_);
v_res_168_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2(v_a_6133__boxed_165_, v_as_162_, v_i_boxed_166_, v_stop_boxed_167_);
lean_dec_ref(v_as_162_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(lean_object* v_f_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v___x_176_; 
lean_inc_ref(v_f_170_);
v___x_176_ = l_Lean_Meta_isProof(v_f_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_301_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_301_ == 0)
{
v___x_179_ = v___x_176_;
v_isShared_180_ = v_isSharedCheck_301_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_176_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_301_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
uint8_t v___x_181_; 
v___x_181_ = lean_unbox(v_a_177_);
if (v___x_181_ == 0)
{
uint8_t v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
lean_del_object(v___x_179_);
v___x_182_ = 1;
v___x_183_ = lean_box(0);
lean_inc_ref(v_f_170_);
v___x_184_ = l_Lean_Meta_getFunInfo(v_f_170_, v___x_183_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_288_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_288_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_288_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_288_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; 
lean_inc_ref(v_f_170_);
v___x_189_ = l_Lean_Meta_getCongrSimpKinds(v_f_170_, v_a_185_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_279_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_279_ == 0)
{
v___x_192_ = v___x_189_;
v_isShared_193_ = v_isSharedCheck_279_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_189_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_279_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___y_200_; lean_object* v___y_201_; lean_object* v___y_202_; lean_object* v___y_203_; lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___y_230_; uint8_t v___x_249_; 
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_array_get_size(v_a_190_);
v___x_249_ = lean_nat_dec_lt(v___x_227_, v___x_228_);
if (v___x_249_ == 0)
{
lean_dec(v_a_185_);
lean_dec_ref(v_f_170_);
v___y_230_ = v___x_182_;
goto v___jp_229_;
}
else
{
if (v___x_249_ == 0)
{
lean_dec(v_a_185_);
lean_dec_ref(v_f_170_);
v___y_230_ = v___x_182_;
goto v___jp_229_;
}
else
{
size_t v___x_250_; size_t v___x_251_; uint8_t v___x_252_; uint8_t v___x_253_; 
v___x_250_ = ((size_t)0ULL);
v___x_251_ = lean_usize_of_nat(v___x_228_);
v___x_252_ = lean_unbox(v_a_177_);
v___x_253_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__2(v___x_252_, v_a_190_, v___x_250_, v___x_251_);
if (v___x_253_ == 0)
{
lean_dec(v_a_185_);
lean_dec_ref(v_f_170_);
v___y_230_ = v___x_249_;
goto v___jp_229_;
}
else
{
lean_del_object(v___x_192_);
lean_del_object(v___x_187_);
lean_dec(v_a_177_);
if (lean_obj_tag(v_f_170_) == 4)
{
lean_object* v_declName_254_; lean_object* v_us_255_; lean_object* v___x_256_; 
v_declName_254_ = lean_ctor_get(v_f_170_, 0);
v_us_255_ = lean_ctor_get(v_f_170_, 1);
lean_inc(v_us_255_);
lean_inc(v_declName_254_);
v___x_256_ = l_Lean_Meta_mkCongrSimpForConst_x3f(v_declName_254_, v_us_255_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_270_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_270_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_270_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_270_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
if (lean_obj_tag(v_a_257_) == 1)
{
lean_object* v_val_261_; lean_object* v_argKinds_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_val_261_ = lean_ctor_get(v_a_257_, 0);
lean_inc(v_val_261_);
lean_dec_ref_known(v_a_257_, 1);
v_argKinds_262_ = lean_ctor_get(v_val_261_, 2);
v___x_263_ = lean_array_get_size(v_argKinds_262_);
v___x_264_ = lean_nat_dec_eq(v___x_263_, v___x_228_);
if (v___x_264_ == 0)
{
lean_dec(v_val_261_);
lean_del_object(v___x_259_);
v___y_200_ = v_a_171_;
v___y_201_ = v_a_172_;
v___y_202_ = v_a_173_;
v___y_203_ = v_a_174_;
goto v___jp_199_;
}
else
{
uint8_t v___x_265_; 
v___x_265_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg(v_argKinds_262_, v_a_190_, v___x_263_);
if (v___x_265_ == 0)
{
lean_dec(v_val_261_);
lean_del_object(v___x_259_);
v___y_200_ = v_a_171_;
v___y_201_ = v_a_172_;
v___y_202_ = v_a_173_;
v___y_203_ = v_a_174_;
goto v___jp_199_;
}
else
{
lean_object* v___x_266_; lean_object* v___x_268_; 
lean_dec_ref_known(v_f_170_, 2);
lean_dec(v_a_190_);
lean_dec(v_a_185_);
v___x_266_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrTheoremInfo(v_val_261_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_266_);
v___x_268_ = v___x_259_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_266_);
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
lean_del_object(v___x_259_);
lean_dec(v_a_257_);
v___y_200_ = v_a_171_;
v___y_201_ = v_a_172_;
v___y_202_ = v_a_173_;
v___y_203_ = v_a_174_;
goto v___jp_199_;
}
}
}
else
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
lean_dec_ref_known(v_f_170_, 2);
lean_dec(v_a_190_);
lean_dec(v_a_185_);
v_a_271_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v___x_256_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_256_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
else
{
v___y_200_ = v_a_171_;
v___y_201_ = v_a_172_;
v___y_202_ = v_a_173_;
v___y_203_ = v_a_174_;
goto v___jp_199_;
}
}
}
}
v___jp_194_:
{
lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_195_ = lean_box(0);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_195_);
v___x_197_ = v___x_192_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
v___jp_199_:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Meta_mkCongrSimpCore_x3f(v_f_170_, v_a_185_, v_a_190_, v___x_182_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_218_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_218_ == 0)
{
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_218_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_218_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
if (lean_obj_tag(v_a_205_) == 1)
{
lean_object* v_val_209_; lean_object* v___x_210_; lean_object* v___x_212_; 
v_val_209_ = lean_ctor_get(v_a_205_, 0);
lean_inc(v_val_209_);
lean_dec_ref_known(v_a_205_, 1);
v___x_210_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrTheoremInfo(v_val_209_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_210_);
v___x_212_ = v___x_207_;
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
else
{
lean_object* v___x_214_; lean_object* v___x_216_; 
lean_dec(v_a_205_);
v___x_214_ = lean_box(0);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_214_);
v___x_216_ = v___x_207_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
else
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_226_; 
v_a_219_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_226_ == 0)
{
v___x_221_ = v___x_204_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_204_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_a_219_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
v___jp_229_:
{
uint8_t v___x_231_; 
v___x_231_ = lean_nat_dec_lt(v___x_227_, v___x_228_);
if (v___x_231_ == 0)
{
lean_dec(v_a_190_);
lean_del_object(v___x_187_);
lean_dec(v_a_177_);
goto v___jp_194_;
}
else
{
if (v___x_231_ == 0)
{
lean_dec(v_a_190_);
lean_del_object(v___x_187_);
lean_dec(v_a_177_);
goto v___jp_194_;
}
else
{
size_t v___x_232_; size_t v___x_233_; uint8_t v___x_234_; uint8_t v___x_235_; 
v___x_232_ = ((size_t)0ULL);
v___x_233_ = lean_usize_of_nat(v___x_228_);
v___x_234_ = lean_unbox(v_a_177_);
lean_dec(v_a_177_);
v___x_235_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__0(v___y_230_, v___x_234_, v_a_190_, v___x_232_, v___x_233_);
if (v___x_235_ == 0)
{
lean_dec(v_a_190_);
lean_del_object(v___x_187_);
goto v___jp_194_;
}
else
{
lean_object* v___x_236_; 
lean_del_object(v___x_192_);
v___x_236_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_isFixedPrefix_x3f(v_a_190_);
if (lean_obj_tag(v___x_236_) == 1)
{
lean_object* v_val_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
lean_dec(v_a_190_);
v_val_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_val_237_);
lean_dec_ref_known(v___x_236_, 1);
v___x_238_ = lean_nat_sub(v___x_228_, v_val_237_);
v___x_239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_239_, 0, v_val_237_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_239_);
v___x_241_ = v___x_187_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
else
{
size_t v_sz_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
lean_dec(v___x_236_);
v_sz_243_ = lean_array_size(v_a_190_);
v___x_244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__1(v_sz_243_, v___x_232_, v_a_190_);
v___x_245_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_245_);
v___x_247_ = v___x_187_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
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
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
lean_del_object(v___x_187_);
lean_dec(v_a_185_);
lean_dec(v_a_177_);
lean_dec_ref(v_f_170_);
v_a_280_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v___x_189_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_189_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_dec(v_a_177_);
lean_dec_ref(v_f_170_);
v_a_289_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_184_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_184_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
else
{
lean_object* v___x_297_; lean_object* v___x_299_; 
lean_dec(v_a_177_);
lean_dec_ref(v_f_170_);
v___x_297_ = lean_box(0);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_297_);
v___x_299_ = v___x_179_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
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
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
lean_dec_ref(v_f_170_);
v_a_302_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_176_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_176_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg___boxed(lean_object* v_f_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(v_f_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
lean_dec(v_a_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo(lean_object* v_f_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(v_f_317_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___boxed(lean_object* v_f_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo(v_f_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
return v_res_334_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3(lean_object* v_xs_335_, lean_object* v_ys_336_, lean_object* v_hsz_337_, lean_object* v_x_338_, lean_object* v_x_339_){
_start:
{
uint8_t v___x_340_; 
v___x_340_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___redArg(v_xs_335_, v_ys_336_, v_x_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3___boxed(lean_object* v_xs_341_, lean_object* v_ys_342_, lean_object* v_hsz_343_, lean_object* v_x_344_, lean_object* v_x_345_){
_start:
{
uint8_t v_res_346_; lean_object* v_r_347_; 
v_res_346_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo_spec__3(v_xs_341_, v_ys_342_, v_hsz_343_, v_x_344_, v_x_345_);
lean_dec_ref(v_ys_342_);
lean_dec_ref(v_xs_341_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_348_, lean_object* v_x_349_, lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
lean_object* v_ks_352_; lean_object* v_vs_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_379_; 
v_ks_352_ = lean_ctor_get(v_x_348_, 0);
v_vs_353_ = lean_ctor_get(v_x_348_, 1);
v_isSharedCheck_379_ = !lean_is_exclusive(v_x_348_);
if (v_isSharedCheck_379_ == 0)
{
v___x_355_ = v_x_348_;
v_isShared_356_ = v_isSharedCheck_379_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_vs_353_);
lean_inc(v_ks_352_);
lean_dec(v_x_348_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_379_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = lean_array_get_size(v_ks_352_);
v___x_358_ = lean_nat_dec_lt(v_x_349_, v___x_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
lean_dec(v_x_349_);
v___x_359_ = lean_array_push(v_ks_352_, v_x_350_);
v___x_360_ = lean_array_push(v_vs_353_, v_x_351_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 1, v___x_360_);
lean_ctor_set(v___x_355_, 0, v___x_359_);
v___x_362_ = v___x_355_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v___x_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
else
{
lean_object* v_k_x27_364_; size_t v___x_365_; size_t v___x_366_; uint8_t v___x_367_; 
v_k_x27_364_ = lean_array_fget_borrowed(v_ks_352_, v_x_349_);
v___x_365_ = lean_ptr_addr(v_x_350_);
v___x_366_ = lean_ptr_addr(v_k_x27_364_);
v___x_367_ = lean_usize_dec_eq(v___x_365_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_369_; 
if (v_isShared_356_ == 0)
{
v___x_369_ = v___x_355_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_ks_352_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_vs_353_);
v___x_369_ = v_reuseFailAlloc_373_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_unsigned_to_nat(1u);
v___x_371_ = lean_nat_add(v_x_349_, v___x_370_);
lean_dec(v_x_349_);
v_x_348_ = v___x_369_;
v_x_349_ = v___x_371_;
goto _start;
}
}
else
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_374_ = lean_array_fset(v_ks_352_, v_x_349_, v_x_350_);
v___x_375_ = lean_array_fset(v_vs_353_, v_x_349_, v_x_351_);
lean_dec(v_x_349_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 1, v___x_375_);
lean_ctor_set(v___x_355_, 0, v___x_374_);
v___x_377_ = v___x_355_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v___x_375_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4___redArg(lean_object* v_n_380_, lean_object* v_k_381_, lean_object* v_v_382_){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5___redArg(v_n_380_, v___x_383_, v_k_381_, v_v_382_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(lean_object* v_x_386_, size_t v_x_387_, size_t v_x_388_, lean_object* v_x_389_, lean_object* v_x_390_){
_start:
{
if (lean_obj_tag(v_x_386_) == 0)
{
lean_object* v_es_391_; size_t v___x_392_; size_t v___x_393_; lean_object* v_j_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v_es_391_ = lean_ctor_get(v_x_386_, 0);
v___x_392_ = ((size_t)31ULL);
v___x_393_ = lean_usize_land(v_x_387_, v___x_392_);
v_j_394_ = lean_usize_to_nat(v___x_393_);
v___x_395_ = lean_array_get_size(v_es_391_);
v___x_396_ = lean_nat_dec_lt(v_j_394_, v___x_395_);
if (v___x_396_ == 0)
{
lean_dec(v_j_394_);
lean_dec(v_x_390_);
lean_dec_ref(v_x_389_);
return v_x_386_;
}
else
{
lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_437_; 
lean_inc_ref(v_es_391_);
v_isSharedCheck_437_ = !lean_is_exclusive(v_x_386_);
if (v_isSharedCheck_437_ == 0)
{
lean_object* v_unused_438_; 
v_unused_438_ = lean_ctor_get(v_x_386_, 0);
lean_dec(v_unused_438_);
v___x_398_ = v_x_386_;
v_isShared_399_ = v_isSharedCheck_437_;
goto v_resetjp_397_;
}
else
{
lean_dec(v_x_386_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_437_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v_v_400_; lean_object* v___x_401_; lean_object* v_xs_x27_402_; lean_object* v___y_404_; 
v_v_400_ = lean_array_fget(v_es_391_, v_j_394_);
v___x_401_ = lean_box(0);
v_xs_x27_402_ = lean_array_fset(v_es_391_, v_j_394_, v___x_401_);
switch(lean_obj_tag(v_v_400_))
{
case 0:
{
lean_object* v_key_409_; lean_object* v_val_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_422_; 
v_key_409_ = lean_ctor_get(v_v_400_, 0);
v_val_410_ = lean_ctor_get(v_v_400_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v_v_400_);
if (v_isSharedCheck_422_ == 0)
{
v___x_412_ = v_v_400_;
v_isShared_413_ = v_isSharedCheck_422_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_val_410_);
lean_inc(v_key_409_);
lean_dec(v_v_400_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_422_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
size_t v___x_414_; size_t v___x_415_; uint8_t v___x_416_; 
v___x_414_ = lean_ptr_addr(v_x_389_);
v___x_415_ = lean_ptr_addr(v_key_409_);
v___x_416_ = lean_usize_dec_eq(v___x_414_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; lean_object* v___x_418_; 
lean_del_object(v___x_412_);
v___x_417_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_409_, v_val_410_, v_x_389_, v_x_390_);
v___x_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
v___y_404_ = v___x_418_;
goto v___jp_403_;
}
else
{
lean_object* v___x_420_; 
lean_dec(v_val_410_);
lean_dec(v_key_409_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v_x_390_);
lean_ctor_set(v___x_412_, 0, v_x_389_);
v___x_420_ = v___x_412_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_x_389_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_x_390_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
v___y_404_ = v___x_420_;
goto v___jp_403_;
}
}
}
}
case 1:
{
lean_object* v_node_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_435_; 
v_node_423_ = lean_ctor_get(v_v_400_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v_v_400_);
if (v_isSharedCheck_435_ == 0)
{
v___x_425_ = v_v_400_;
v_isShared_426_ = v_isSharedCheck_435_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_node_423_);
lean_dec(v_v_400_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_435_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
size_t v___x_427_; size_t v___x_428_; size_t v___x_429_; size_t v___x_430_; lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_427_ = ((size_t)5ULL);
v___x_428_ = lean_usize_shift_right(v_x_387_, v___x_427_);
v___x_429_ = ((size_t)1ULL);
v___x_430_ = lean_usize_add(v_x_388_, v___x_429_);
v___x_431_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_node_423_, v___x_428_, v___x_430_, v_x_389_, v_x_390_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_431_);
v___x_433_ = v___x_425_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
v___y_404_ = v___x_433_;
goto v___jp_403_;
}
}
}
default: 
{
lean_object* v___x_436_; 
v___x_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_436_, 0, v_x_389_);
lean_ctor_set(v___x_436_, 1, v_x_390_);
v___y_404_ = v___x_436_;
goto v___jp_403_;
}
}
v___jp_403_:
{
lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_405_ = lean_array_fset(v_xs_x27_402_, v_j_394_, v___y_404_);
lean_dec(v_j_394_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_405_);
v___x_407_ = v___x_398_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
else
{
lean_object* v_ks_439_; lean_object* v_vs_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_458_; 
v_ks_439_ = lean_ctor_get(v_x_386_, 0);
v_vs_440_ = lean_ctor_get(v_x_386_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v_x_386_);
if (v_isSharedCheck_458_ == 0)
{
v___x_442_ = v_x_386_;
v_isShared_443_ = v_isSharedCheck_458_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_vs_440_);
lean_inc(v_ks_439_);
lean_dec(v_x_386_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_458_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_ks_439_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_vs_440_);
v___x_445_ = v_reuseFailAlloc_457_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v_newNode_446_; size_t v___x_447_; uint8_t v___x_448_; 
v_newNode_446_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4___redArg(v___x_445_, v_x_389_, v_x_390_);
v___x_447_ = ((size_t)7ULL);
v___x_448_ = lean_usize_dec_le(v___x_447_, v_x_388_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_449_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_446_);
v___x_450_ = lean_unsigned_to_nat(4u);
v___x_451_ = lean_nat_dec_lt(v___x_449_, v___x_450_);
lean_dec(v___x_449_);
if (v___x_451_ == 0)
{
lean_object* v_ks_452_; lean_object* v_vs_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v_ks_452_ = lean_ctor_get(v_newNode_446_, 0);
lean_inc_ref(v_ks_452_);
v_vs_453_ = lean_ctor_get(v_newNode_446_, 1);
lean_inc_ref(v_vs_453_);
lean_dec_ref(v_newNode_446_);
v___x_454_ = lean_unsigned_to_nat(0u);
v___x_455_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___closed__0);
v___x_456_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(v_x_388_, v_ks_452_, v_vs_453_, v___x_454_, v___x_455_);
lean_dec_ref(v_vs_453_);
lean_dec_ref(v_ks_452_);
return v___x_456_;
}
else
{
return v_newNode_446_;
}
}
else
{
return v_newNode_446_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(size_t v_depth_459_, lean_object* v_keys_460_, lean_object* v_vals_461_, lean_object* v_i_462_, lean_object* v_entries_463_){
_start:
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = lean_array_get_size(v_keys_460_);
v___x_465_ = lean_nat_dec_lt(v_i_462_, v___x_464_);
if (v___x_465_ == 0)
{
lean_dec(v_i_462_);
return v_entries_463_;
}
else
{
lean_object* v_k_466_; lean_object* v_v_467_; size_t v___x_468_; size_t v___x_469_; size_t v___x_470_; uint64_t v___x_471_; size_t v_h_472_; size_t v___x_473_; lean_object* v___x_474_; size_t v___x_475_; size_t v___x_476_; size_t v___x_477_; size_t v_h_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v_k_466_ = lean_array_fget_borrowed(v_keys_460_, v_i_462_);
v_v_467_ = lean_array_fget_borrowed(v_vals_461_, v_i_462_);
v___x_468_ = lean_ptr_addr(v_k_466_);
v___x_469_ = ((size_t)3ULL);
v___x_470_ = lean_usize_shift_right(v___x_468_, v___x_469_);
v___x_471_ = lean_usize_to_uint64(v___x_470_);
v_h_472_ = lean_uint64_to_usize(v___x_471_);
v___x_473_ = ((size_t)5ULL);
v___x_474_ = lean_unsigned_to_nat(1u);
v___x_475_ = ((size_t)1ULL);
v___x_476_ = lean_usize_sub(v_depth_459_, v___x_475_);
v___x_477_ = lean_usize_mul(v___x_473_, v___x_476_);
v_h_478_ = lean_usize_shift_right(v_h_472_, v___x_477_);
v___x_479_ = lean_nat_add(v_i_462_, v___x_474_);
lean_dec(v_i_462_);
lean_inc(v_v_467_);
lean_inc(v_k_466_);
v___x_480_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_entries_463_, v_h_478_, v_depth_459_, v_k_466_, v_v_467_);
v_i_462_ = v___x_479_;
v_entries_463_ = v___x_480_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_482_, lean_object* v_keys_483_, lean_object* v_vals_484_, lean_object* v_i_485_, lean_object* v_entries_486_){
_start:
{
size_t v_depth_boxed_487_; lean_object* v_res_488_; 
v_depth_boxed_487_ = lean_unbox_usize(v_depth_482_);
lean_dec(v_depth_482_);
v_res_488_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(v_depth_boxed_487_, v_keys_483_, v_vals_484_, v_i_485_, v_entries_486_);
lean_dec_ref(v_vals_484_);
lean_dec_ref(v_keys_483_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg___boxed(lean_object* v_x_489_, lean_object* v_x_490_, lean_object* v_x_491_, lean_object* v_x_492_, lean_object* v_x_493_){
_start:
{
size_t v_x_2566__boxed_494_; size_t v_x_2567__boxed_495_; lean_object* v_res_496_; 
v_x_2566__boxed_494_ = lean_unbox_usize(v_x_490_);
lean_dec(v_x_490_);
v_x_2567__boxed_495_ = lean_unbox_usize(v_x_491_);
lean_dec(v_x_491_);
v_res_496_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_x_489_, v_x_2566__boxed_494_, v_x_2567__boxed_495_, v_x_492_, v_x_493_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1___redArg(lean_object* v_x_497_, lean_object* v_x_498_, lean_object* v_x_499_){
_start:
{
size_t v___x_500_; size_t v___x_501_; size_t v___x_502_; uint64_t v___x_503_; size_t v___x_504_; size_t v___x_505_; lean_object* v___x_506_; 
v___x_500_ = lean_ptr_addr(v_x_498_);
v___x_501_ = ((size_t)3ULL);
v___x_502_ = lean_usize_shift_right(v___x_500_, v___x_501_);
v___x_503_ = lean_usize_to_uint64(v___x_502_);
v___x_504_ = lean_uint64_to_usize(v___x_503_);
v___x_505_ = ((size_t)1ULL);
v___x_506_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_x_497_, v___x_504_, v___x_505_, v_x_498_, v_x_499_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_507_, lean_object* v_vals_508_, lean_object* v_i_509_, lean_object* v_k_510_){
_start:
{
lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = lean_array_get_size(v_keys_507_);
v___x_512_ = lean_nat_dec_lt(v_i_509_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; 
lean_dec(v_i_509_);
v___x_513_ = lean_box(0);
return v___x_513_;
}
else
{
lean_object* v_k_x27_514_; size_t v___x_515_; size_t v___x_516_; uint8_t v___x_517_; 
v_k_x27_514_ = lean_array_fget_borrowed(v_keys_507_, v_i_509_);
v___x_515_ = lean_ptr_addr(v_k_510_);
v___x_516_ = lean_ptr_addr(v_k_x27_514_);
v___x_517_ = lean_usize_dec_eq(v___x_515_, v___x_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = lean_nat_add(v_i_509_, v___x_518_);
lean_dec(v_i_509_);
v_i_509_ = v___x_519_;
goto _start;
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_array_fget_borrowed(v_vals_508_, v_i_509_);
lean_dec(v_i_509_);
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
lean_object* v_key_537_; lean_object* v_val_538_; size_t v___x_539_; size_t v___x_540_; uint8_t v___x_541_; 
v_key_537_ = lean_ctor_get(v___x_536_, 0);
v_val_538_ = lean_ctor_get(v___x_536_, 1);
v___x_539_ = lean_ptr_addr(v_x_530_);
v___x_540_ = lean_ptr_addr(v_key_537_);
v___x_541_ = lean_usize_dec_eq(v___x_539_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; 
v___x_542_ = lean_box(0);
return v___x_542_;
}
else
{
lean_object* v___x_543_; 
lean_inc(v_val_538_);
v___x_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_543_, 0, v_val_538_);
return v___x_543_;
}
}
case 1:
{
lean_object* v_node_544_; size_t v___x_545_; size_t v___x_546_; 
v_node_544_ = lean_ctor_get(v___x_536_, 0);
v___x_545_ = ((size_t)5ULL);
v___x_546_ = lean_usize_shift_right(v_x_529_, v___x_545_);
v_x_528_ = v_node_544_;
v_x_529_ = v___x_546_;
goto _start;
}
default: 
{
lean_object* v___x_548_; 
v___x_548_ = lean_box(0);
return v___x_548_;
}
}
}
else
{
lean_object* v_ks_549_; lean_object* v_vs_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_ks_549_ = lean_ctor_get(v_x_528_, 0);
v_vs_550_ = lean_ctor_get(v_x_528_, 1);
v___x_551_ = lean_unsigned_to_nat(0u);
v___x_552_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(v_ks_549_, v_vs_550_, v___x_551_, v_x_530_);
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg___boxed(lean_object* v_x_553_, lean_object* v_x_554_, lean_object* v_x_555_){
_start:
{
size_t v_x_2767__boxed_556_; lean_object* v_res_557_; 
v_x_2767__boxed_556_ = lean_unbox_usize(v_x_554_);
lean_dec(v_x_554_);
v_res_557_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(v_x_553_, v_x_2767__boxed_556_, v_x_555_);
lean_dec_ref(v_x_555_);
lean_dec_ref(v_x_553_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
size_t v___x_560_; size_t v___x_561_; size_t v___x_562_; uint64_t v___x_563_; size_t v___x_564_; lean_object* v___x_565_; 
v___x_560_ = lean_ptr_addr(v_x_559_);
v___x_561_ = ((size_t)3ULL);
v___x_562_ = lean_usize_shift_right(v___x_560_, v___x_561_);
v___x_563_ = lean_usize_to_uint64(v___x_562_);
v___x_564_ = lean_uint64_to_usize(v___x_563_);
v___x_565_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(v_x_558_, v___x_564_, v_x_559_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg___boxed(lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(v_x_566_, v_x_567_);
lean_dec_ref(v_x_567_);
lean_dec_ref(v_x_566_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCongrInfo___redArg(lean_object* v_f_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v___x_576_; lean_object* v_congrInfo_577_; lean_object* v___x_578_; 
v___x_576_ = lean_st_ref_get(v_a_570_);
v_congrInfo_577_ = lean_ctor_get(v___x_576_, 7);
lean_inc_ref(v_congrInfo_577_);
lean_dec(v___x_576_);
v___x_578_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(v_congrInfo_577_, v_f_569_);
lean_dec_ref(v_congrInfo_577_);
if (lean_obj_tag(v___x_578_) == 1)
{
lean_object* v_val_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_dec_ref(v_f_569_);
v_val_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_val_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set_tag(v___x_581_, 0);
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_val_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
else
{
lean_object* v___x_587_; 
lean_dec(v___x_578_);
lean_inc_ref(v_f_569_);
v___x_587_ = l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_mkCongrInfo___redArg(v_f_569_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_619_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_619_ == 0)
{
v___x_590_ = v___x_587_;
v_isShared_591_ = v_isSharedCheck_619_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_587_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_619_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v_share_593_; lean_object* v_maxFVar_594_; lean_object* v_proofInstInfo_595_; lean_object* v_proofInstInfoFVar_596_; lean_object* v_letValue_597_; lean_object* v_inferType_598_; lean_object* v_getLevel_599_; lean_object* v_congrInfo_600_; lean_object* v_defEqI_601_; lean_object* v_extensions_602_; lean_object* v_issues_603_; lean_object* v_canon_604_; lean_object* v_instanceOverrides_605_; uint8_t v_debug_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_618_; 
v___x_592_ = lean_st_ref_take(v_a_570_);
v_share_593_ = lean_ctor_get(v___x_592_, 0);
v_maxFVar_594_ = lean_ctor_get(v___x_592_, 1);
v_proofInstInfo_595_ = lean_ctor_get(v___x_592_, 2);
v_proofInstInfoFVar_596_ = lean_ctor_get(v___x_592_, 3);
v_letValue_597_ = lean_ctor_get(v___x_592_, 4);
v_inferType_598_ = lean_ctor_get(v___x_592_, 5);
v_getLevel_599_ = lean_ctor_get(v___x_592_, 6);
v_congrInfo_600_ = lean_ctor_get(v___x_592_, 7);
v_defEqI_601_ = lean_ctor_get(v___x_592_, 8);
v_extensions_602_ = lean_ctor_get(v___x_592_, 9);
v_issues_603_ = lean_ctor_get(v___x_592_, 10);
v_canon_604_ = lean_ctor_get(v___x_592_, 11);
v_instanceOverrides_605_ = lean_ctor_get(v___x_592_, 12);
v_debug_606_ = lean_ctor_get_uint8(v___x_592_, sizeof(void*)*13);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_618_ == 0)
{
v___x_608_ = v___x_592_;
v_isShared_609_ = v_isSharedCheck_618_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_instanceOverrides_605_);
lean_inc(v_canon_604_);
lean_inc(v_issues_603_);
lean_inc(v_extensions_602_);
lean_inc(v_defEqI_601_);
lean_inc(v_congrInfo_600_);
lean_inc(v_getLevel_599_);
lean_inc(v_inferType_598_);
lean_inc(v_letValue_597_);
lean_inc(v_proofInstInfoFVar_596_);
lean_inc(v_proofInstInfo_595_);
lean_inc(v_maxFVar_594_);
lean_inc(v_share_593_);
lean_dec(v___x_592_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_618_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_612_; 
lean_inc(v_a_588_);
v___x_610_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1___redArg(v_congrInfo_600_, v_f_569_, v_a_588_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 7, v___x_610_);
v___x_612_ = v___x_608_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_share_593_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_maxFVar_594_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_proofInstInfo_595_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v_proofInstInfoFVar_596_);
lean_ctor_set(v_reuseFailAlloc_617_, 4, v_letValue_597_);
lean_ctor_set(v_reuseFailAlloc_617_, 5, v_inferType_598_);
lean_ctor_set(v_reuseFailAlloc_617_, 6, v_getLevel_599_);
lean_ctor_set(v_reuseFailAlloc_617_, 7, v___x_610_);
lean_ctor_set(v_reuseFailAlloc_617_, 8, v_defEqI_601_);
lean_ctor_set(v_reuseFailAlloc_617_, 9, v_extensions_602_);
lean_ctor_set(v_reuseFailAlloc_617_, 10, v_issues_603_);
lean_ctor_set(v_reuseFailAlloc_617_, 11, v_canon_604_);
lean_ctor_set(v_reuseFailAlloc_617_, 12, v_instanceOverrides_605_);
lean_ctor_set_uint8(v_reuseFailAlloc_617_, sizeof(void*)*13, v_debug_606_);
v___x_612_ = v_reuseFailAlloc_617_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_613_ = lean_st_ref_put(v_a_570_, v___x_612_);
if (v_isShared_591_ == 0)
{
v___x_615_ = v___x_590_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_588_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_569_);
return v___x_587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCongrInfo___redArg___boxed(lean_object* v_f_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_Meta_Sym_getCongrInfo___redArg(v_f_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCongrInfo(lean_object* v_f_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_Meta_Sym_getCongrInfo___redArg(v_f_628_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCongrInfo___boxed(lean_object* v_f_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_Meta_Sym_getCongrInfo(v_f_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0(lean_object* v_00_u03b2_646_, lean_object* v_x_647_, lean_object* v_x_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___redArg(v_x_647_, v_x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0___boxed(lean_object* v_00_u03b2_650_, lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0(v_00_u03b2_650_, v_x_651_, v_x_652_);
lean_dec_ref(v_x_652_);
lean_dec_ref(v_x_651_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1(lean_object* v_00_u03b2_654_, lean_object* v_x_655_, lean_object* v_x_656_, lean_object* v_x_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1___redArg(v_x_655_, v_x_656_, v_x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0(lean_object* v_00_u03b2_659_, lean_object* v_x_660_, size_t v_x_661_, lean_object* v_x_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___redArg(v_x_660_, v_x_661_, v_x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0___boxed(lean_object* v_00_u03b2_664_, lean_object* v_x_665_, lean_object* v_x_666_, lean_object* v_x_667_){
_start:
{
size_t v_x_2919__boxed_668_; lean_object* v_res_669_; 
v_x_2919__boxed_668_ = lean_unbox_usize(v_x_666_);
lean_dec(v_x_666_);
v_res_669_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0(v_00_u03b2_664_, v_x_665_, v_x_2919__boxed_668_, v_x_667_);
lean_dec_ref(v_x_667_);
lean_dec_ref(v_x_665_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2(lean_object* v_00_u03b2_670_, lean_object* v_x_671_, size_t v_x_672_, size_t v_x_673_, lean_object* v_x_674_, lean_object* v_x_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___redArg(v_x_671_, v_x_672_, v_x_673_, v_x_674_, v_x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2___boxed(lean_object* v_00_u03b2_677_, lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v_x_682_){
_start:
{
size_t v_x_2930__boxed_683_; size_t v_x_2931__boxed_684_; lean_object* v_res_685_; 
v_x_2930__boxed_683_ = lean_unbox_usize(v_x_679_);
lean_dec(v_x_679_);
v_x_2931__boxed_684_ = lean_unbox_usize(v_x_680_);
lean_dec(v_x_680_);
v_res_685_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2(v_00_u03b2_677_, v_x_678_, v_x_2930__boxed_683_, v_x_2931__boxed_684_, v_x_681_, v_x_682_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_686_, lean_object* v_keys_687_, lean_object* v_vals_688_, lean_object* v_heq_689_, lean_object* v_i_690_, lean_object* v_k_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___redArg(v_keys_687_, v_vals_688_, v_i_690_, v_k_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_693_, lean_object* v_keys_694_, lean_object* v_vals_695_, lean_object* v_heq_696_, lean_object* v_i_697_, lean_object* v_k_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_getCongrInfo_spec__0_spec__0_spec__1(v_00_u03b2_693_, v_keys_694_, v_vals_695_, v_heq_696_, v_i_697_, v_k_698_);
lean_dec_ref(v_k_698_);
lean_dec_ref(v_vals_695_);
lean_dec_ref(v_keys_694_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_700_, lean_object* v_n_701_, lean_object* v_k_702_, lean_object* v_v_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4___redArg(v_n_701_, v_k_702_, v_v_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_705_, size_t v_depth_706_, lean_object* v_keys_707_, lean_object* v_vals_708_, lean_object* v_heq_709_, lean_object* v_i_710_, lean_object* v_entries_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___redArg(v_depth_706_, v_keys_707_, v_vals_708_, v_i_710_, v_entries_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_713_, lean_object* v_depth_714_, lean_object* v_keys_715_, lean_object* v_vals_716_, lean_object* v_heq_717_, lean_object* v_i_718_, lean_object* v_entries_719_){
_start:
{
size_t v_depth_boxed_720_; lean_object* v_res_721_; 
v_depth_boxed_720_ = lean_unbox_usize(v_depth_714_);
lean_dec(v_depth_714_);
v_res_721_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__5(v_00_u03b2_713_, v_depth_boxed_720_, v_keys_715_, v_vals_716_, v_heq_717_, v_i_718_, v_entries_719_);
lean_dec_ref(v_vals_716_);
lean_dec_ref(v_keys_715_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_722_, lean_object* v_x_723_, lean_object* v_x_724_, lean_object* v_x_725_, lean_object* v_x_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_getCongrInfo_spec__1_spec__2_spec__4_spec__5___redArg(v_x_723_, v_x_724_, v_x_725_, v_x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0(lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
if (lean_obj_tag(v_a_730_) == 0)
{
lean_object* v___x_732_; 
v___x_732_ = l_List_reverse___redArg(v_a_731_);
return v___x_732_;
}
else
{
lean_object* v_head_733_; lean_object* v_tail_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_749_; 
v_head_733_ = lean_ctor_get(v_a_730_, 0);
v_tail_734_ = lean_ctor_get(v_a_730_, 1);
v_isSharedCheck_749_ = !lean_is_exclusive(v_a_730_);
if (v_isSharedCheck_749_ == 0)
{
v___x_736_ = v_a_730_;
v_isShared_737_ = v_isSharedCheck_749_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_tail_734_);
lean_inc(v_head_733_);
lean_dec(v_a_730_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_749_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___y_739_; uint8_t v___x_746_; 
v___x_746_ = lean_unbox(v_head_733_);
lean_dec(v_head_733_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; 
v___x_747_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__0));
v___y_739_ = v___x_747_;
goto v___jp_738_;
}
else
{
lean_object* v___x_748_; 
v___x_748_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0___closed__1));
v___y_739_ = v___x_748_;
goto v___jp_738_;
}
v___jp_738_:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_743_; 
lean_inc_ref(v___y_739_);
v___x_740_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_740_, 0, v___y_739_);
v___x_741_ = l_Lean_MessageData_ofFormat(v___x_740_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 1, v_a_731_);
lean_ctor_set(v___x_736_, 0, v___x_741_);
v___x_743_ = v___x_736_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_a_731_);
v___x_743_ = v_reuseFailAlloc_745_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
v_a_730_ = v_tail_734_;
v_a_731_ = v___x_743_;
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
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__1));
v___x_754_ = l_Lean_MessageData_ofFormat(v___x_753_);
return v___x_754_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__3));
v___x_757_ = l_Lean_stringToMessageData(v___x_756_);
return v___x_757_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__5));
v___x_760_ = l_Lean_stringToMessageData(v___x_759_);
return v___x_760_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__7));
v___x_763_ = l_Lean_stringToMessageData(v___x_762_);
return v___x_763_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__9));
v___x_766_ = l_Lean_stringToMessageData(v___x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData(lean_object* v_x_767_){
_start:
{
switch(lean_obj_tag(v_x_767_))
{
case 0:
{
lean_object* v___x_768_; 
v___x_768_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__2);
return v___x_768_;
}
case 1:
{
lean_object* v_prefixSize_769_; lean_object* v_suffixSize_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_787_; 
v_prefixSize_769_ = lean_ctor_get(v_x_767_, 0);
v_suffixSize_770_ = lean_ctor_get(v_x_767_, 1);
v_isSharedCheck_787_ = !lean_is_exclusive(v_x_767_);
if (v_isSharedCheck_787_ == 0)
{
v___x_772_ = v_x_767_;
v_isShared_773_ = v_isSharedCheck_787_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_suffixSize_770_);
lean_inc(v_prefixSize_769_);
lean_dec(v_x_767_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_787_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_779_; 
v___x_774_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__4);
v___x_775_ = l_Nat_reprFast(v_prefixSize_769_);
v___x_776_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
v___x_777_ = l_Lean_MessageData_ofFormat(v___x_776_);
if (v_isShared_773_ == 0)
{
lean_ctor_set_tag(v___x_772_, 7);
lean_ctor_set(v___x_772_, 1, v___x_777_);
lean_ctor_set(v___x_772_, 0, v___x_774_);
v___x_779_ = v___x_772_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v___x_777_);
v___x_779_ = v_reuseFailAlloc_786_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_780_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__6);
v___x_781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_779_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = l_Nat_reprFast(v_suffixSize_770_);
v___x_783_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
v___x_784_ = l_Lean_MessageData_ofFormat(v___x_783_);
v___x_785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_781_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
return v___x_785_;
}
}
}
case 2:
{
lean_object* v_rewritable_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v_rewritable_788_ = lean_ctor_get(v_x_767_, 0);
lean_inc_ref(v_rewritable_788_);
lean_dec_ref_known(v_x_767_, 1);
v___x_789_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__8);
v___x_790_ = lean_array_to_list(v_rewritable_788_);
v___x_791_ = lean_box(0);
v___x_792_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData_spec__0(v___x_790_, v___x_791_);
v___x_793_ = l_Lean_MessageData_ofList(v___x_792_);
v___x_794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_789_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
return v___x_794_;
}
default: 
{
lean_object* v_thm_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_805_; 
v_thm_795_ = lean_ctor_get(v_x_767_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v_x_767_);
if (v_isSharedCheck_805_ == 0)
{
lean_object* v_unused_806_; 
v_unused_806_ = lean_ctor_get(v_x_767_, 1);
lean_dec(v_unused_806_);
v___x_797_ = v_x_767_;
v_isShared_798_ = v_isSharedCheck_805_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_thm_795_);
lean_dec(v_x_767_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_805_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v_proof_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_803_; 
v_proof_799_ = lean_ctor_get(v_thm_795_, 1);
lean_inc_ref(v_proof_799_);
lean_dec_ref(v_thm_795_);
v___x_800_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10, &l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10_once, _init_l___private_Lean_Meta_Sym_Simp_CongrInfo_0__Lean_Meta_Sym_CongrInfo_toMessageData___closed__10);
v___x_801_ = l_Lean_MessageData_ofExpr(v_proof_799_);
if (v_isShared_798_ == 0)
{
lean_ctor_set_tag(v___x_797_, 7);
lean_ctor_set(v___x_797_, 1, v___x_801_);
lean_ctor_set(v___x_797_, 0, v___x_800_);
v___x_803_ = v___x_797_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_FunInfo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectLooseBVars(uint8_t builtin);
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
res = runtime_initialize_Lean_Util_CollectLooseBVars(builtin);
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
lean_object* initialize_Lean_Util_CollectLooseBVars(uint8_t builtin);
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
res = initialize_Lean_Util_CollectLooseBVars(builtin);
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
