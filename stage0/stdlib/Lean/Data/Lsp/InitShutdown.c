// Lean compiler output
// Module: Lean.Data.Lsp.InitShutdown
// Imports: public import Lean.Data.Lsp.Capabilities public import Lean.Data.Lsp.Workspace
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Except_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Except_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_pure(lean_object*, lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson(lean_object*);
lean_object* l_Lean_Array_fromJson_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson(lean_object*);
lean_object* l_Lean_Json_getInt_x3f(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonWorkspaceFolder_toJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson(lean_object*);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
lean_object* l_Lean_Lsp_instToJsonClientCapabilities_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1_value;
static const lean_array_object l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonClientInfo_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonClientInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonClientInfo_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonClientInfo___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonClientInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonClientInfo = (const lean_object*)&l_Lean_Lsp_instToJsonClientInfo___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Lsp"};
static const lean_object* l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ClientInfo"};
static const lean_object* l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 238, 15, 87, 0, 217, 57, 54)}};
static const lean_object* l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__4;
static const lean_string_object l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6;
static const lean_ctor_object l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__7_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__9;
static const lean_string_object l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__11;
static const lean_string_object l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "version\?"};
static const lean_object* l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__12 = (const lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__12_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__12_value),LEAN_SCALAR_PTR_LITERAL(251, 148, 229, 74, 154, 149, 54, 79)}};
static const lean_object* l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__13 = (const lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__13_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14;
static lean_once_cell_t l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__15;
static lean_once_cell_t l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__16;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonClientInfo_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonClientInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonClientInfo_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonClientInfo___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonClientInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonClientInfo = (const lean_object*)&l_Lean_Lsp_instFromJsonClientInfo___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_off_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_off_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_off_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_off_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_messages_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_messages_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_messages_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_messages_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_verbose_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_verbose_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_verbose_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_verbose_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonTrace___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unknown trace"};
static const lean_object* l_Lean_Lsp_instFromJsonTrace___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTrace___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTrace___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTrace___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonTrace___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonTrace___lam__0___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonTrace___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "off"};
static const lean_object* l_Lean_Lsp_instFromJsonTrace___lam__0___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonTrace___lam__0___closed__2_value;
static const lean_string_object l_Lean_Lsp_instFromJsonTrace___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "messages"};
static const lean_object* l_Lean_Lsp_instFromJsonTrace___lam__0___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonTrace___lam__0___closed__3_value;
static const lean_string_object l_Lean_Lsp_instFromJsonTrace___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "verbose"};
static const lean_object* l_Lean_Lsp_instFromJsonTrace___lam__0___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonTrace___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTrace___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonTrace___lam__0___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonTrace___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTrace___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonTrace___lam__0___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonTrace___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTrace___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonTrace___lam__0___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonTrace___lam__0___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTrace___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonTrace___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonTrace___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTrace___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonTrace = (const lean_object*)&l_Lean_Lsp_instFromJsonTrace___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_Trace_hasToJson___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTrace___lam__0___closed__2_value)}};
static const lean_object* l_Lean_Lsp_Trace_hasToJson___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_Trace_hasToJson___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_Trace_hasToJson___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTrace___lam__0___closed__3_value)}};
static const lean_object* l_Lean_Lsp_Trace_hasToJson___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_Trace_hasToJson___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_Trace_hasToJson___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTrace___lam__0___closed__4_value)}};
static const lean_object* l_Lean_Lsp_Trace_hasToJson___lam__0___closed__2 = (const lean_object*)&l_Lean_Lsp_Trace_hasToJson___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_hasToJson___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_hasToJson___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_Trace_hasToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_Trace_hasToJson___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_Trace_hasToJson___closed__0 = (const lean_object*)&l_Lean_Lsp_Trace_hasToJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_Trace_hasToJson = (const lean_object*)&l_Lean_Lsp_Trace_hasToJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__1_value;
static const lean_closure_object l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__2_value;
static const lean_closure_object l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__3 = (const lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__3_value;
static const lean_closure_object l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__4 = (const lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__4_value;
static const lean_closure_object l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__5 = (const lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__5_value;
static const lean_closure_object l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__6 = (const lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__6_value;
static const lean_ctor_object l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__1_value)}};
static const lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__7 = (const lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__7_value;
static const lean_ctor_object l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__7_value),((lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__2_value),((lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__3_value),((lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__4_value),((lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__5_value)}};
static const lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__8 = (const lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__8_value;
static const lean_ctor_object l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__8_value),((lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__6_value)}};
static const lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__9 = (const lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonHashSet___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonHashSet___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__9_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__4;
static const lean_string_object l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "Expected array when converting JSON to Std.HashSet"};
static const lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__5_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonHashSet___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonHashSet___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___closed__1_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonHashSet___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__2___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___closed__2_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonHashSet___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___closed__3_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonHashSet___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_map, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonHashSet___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___closed__4_value),((lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___closed__5_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonHashSet___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_pure, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonHashSet___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___closed__5_value),((lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___closed__6_value),((lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___closed__1_value),((lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___closed__2_value),((lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___closed__3_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___closed__7_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonHashSet___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_bind, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonHashSet___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___closed__7_value),((lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___closed__8_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHashSet(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__0_value;
static lean_once_cell_t l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1;
static lean_once_cell_t l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2;
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__5_value)}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__3 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "logDir"};
static const lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LogConfig"};
static const lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 192, 127, 237, 168, 202, 210, 191)}};
static const lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4;
static const lean_string_object l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "logDir\?"};
static const lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__5_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__5_value),LEAN_SCALAR_PTR_LITERAL(55, 28, 145, 131, 179, 39, 161, 166)}};
static const lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9;
static const lean_string_object l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "allowedMethods"};
static const lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__10_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "allowedMethods\?"};
static const lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__11 = (const lean_object*)&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__11_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__11_value),LEAN_SCALAR_PTR_LITERAL(222, 2, 114, 175, 201, 234, 202, 27)}};
static const lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__12 = (const lean_object*)&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__12_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15;
static const lean_string_object l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "disallowedMethods"};
static const lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__16 = (const lean_object*)&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__16_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "disallowedMethods\?"};
static const lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__17 = (const lean_object*)&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__17_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__17_value),LEAN_SCALAR_PTR_LITERAL(58, 140, 160, 10, 33, 165, 180, 230)}};
static const lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__18 = (const lean_object*)&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__18_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLogConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLogConfig_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLogConfig___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLogConfig___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLogConfig = (const lean_object*)&l_Lean_Lsp_instFromJsonLogConfig___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLogConfig_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLogConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLogConfig_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLogConfig___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLogConfig___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLogConfig = (const lean_object*)&l_Lean_Lsp_instToJsonLogConfig___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "hasWidgets"};
static const lean_object* l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "logCfg"};
static const lean_object* l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonInitializationOptions_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonInitializationOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonInitializationOptions_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonInitializationOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonInitializationOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonInitializationOptions = (const lean_object*)&l_Lean_Lsp_instToJsonInitializationOptions___closed__0_value;
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "InitializationOptions"};
static const lean_object* l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(204, 37, 85, 235, 35, 109, 136, 101)}};
static const lean_object* l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3;
static const lean_string_object l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hasWidgets\?"};
static const lean_object* l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(234, 42, 169, 194, 137, 182, 196, 39)}};
static const lean_object* l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8;
static const lean_string_object l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "logCfg\?"};
static const lean_object* l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(163, 188, 40, 245, 81, 147, 236, 19)}};
static const lean_object* l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializationOptions_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonInitializationOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonInitializationOptions_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonInitializationOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializationOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonInitializationOptions = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializationOptions___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "processId"};
static const lean_object* l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "clientInfo"};
static const lean_object* l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "rootUri"};
static const lean_object* l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__2_value;
static const lean_string_object l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "initializationOptions"};
static const lean_object* l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__3_value;
static const lean_string_object l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "capabilities"};
static const lean_object* l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4_value;
static const lean_string_object l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__5_value;
static const lean_string_object l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "workspaceFolders"};
static const lean_object* l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonInitializeParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonInitializeParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonInitializeParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonInitializeParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonInitializeParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonInitializeParams = (const lean_object*)&l_Lean_Lsp_instToJsonInitializeParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializeParams___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonInitializeParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getInt_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonInitializeParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializeParams___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonInitializeParams___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getStr_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonInitializeParams___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializeParams___closed__1_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonInitializeParams___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonClientCapabilities_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonInitializeParams___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializeParams___closed__2_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonInitializeParams___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonInitializeParams___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializeParams___closed__3_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonInitializeParams___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Array_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonInitializeParams___closed__3_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonInitializeParams___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializeParams___closed__4_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonInitializeParams___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonInitializeParams___lam__0, .m_arity = 8, .m_num_fixed = 7, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonInitializeParams___closed__0_value),((lean_object*)&l_Lean_Lsp_instFromJsonClientInfo___closed__0_value),((lean_object*)&l_Lean_Lsp_instFromJsonInitializeParams___closed__1_value),((lean_object*)&l_Lean_Lsp_instFromJsonInitializationOptions___closed__0_value),((lean_object*)&l_Lean_Lsp_instFromJsonInitializeParams___closed__2_value),((lean_object*)&l_Lean_Lsp_instFromJsonInitializeParams___closed__4_value),((lean_object*)&l_Lean_Lsp_instFromJsonTrace___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonInitializeParams___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializeParams___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonInitializeParams = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializeParams___closed__5_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonInitializedParams___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonInitializedParams___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializedParams___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializedParams___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializedParams___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonInitializedParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonInitializedParams___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonInitializedParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializedParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonInitializedParams = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializedParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonInitializedParams___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonInitializedParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonInitializedParams___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonInitializedParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonInitializedParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonInitializedParams = (const lean_object*)&l_Lean_Lsp_instToJsonInitializedParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonServerInfo_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonServerInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonServerInfo_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonServerInfo___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonServerInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonServerInfo = (const lean_object*)&l_Lean_Lsp_instToJsonServerInfo___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ServerInfo"};
static const lean_object* l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 94, 93, 45, 107, 17, 246, 2)}};
static const lean_object* l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonServerInfo_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonServerInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonServerInfo_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonServerInfo___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonServerInfo = (const lean_object*)&l_Lean_Lsp_instFromJsonServerInfo___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeResult_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonInitializeResult_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "serverInfo"};
static const lean_object* l_Lean_Lsp_instToJsonInitializeResult_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonInitializeResult_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonInitializeResult_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonInitializeResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonInitializeResult_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonInitializeResult___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonInitializeResult___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonInitializeResult = (const lean_object*)&l_Lean_Lsp_instToJsonInitializeResult___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "InitializeResult"};
static const lean_object* l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 210, 86, 209, 201, 216, 173, 68)}};
static const lean_object* l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3;
static const lean_ctor_object l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(162, 13, 225, 21, 187, 204, 20, 252)}};
static const lean_object* l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7;
static const lean_string_object l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "serverInfo\?"};
static const lean_object* l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__8_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__8_value),LEAN_SCALAR_PTR_LITERAL(207, 133, 164, 96, 162, 37, 162, 20)}};
static const lean_object* l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__9_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10;
static lean_once_cell_t l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializeResult_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonInitializeResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonInitializeResult_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonInitializeResult___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializeResult___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonInitializeResult = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializeResult___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__0(lean_object* v_k_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v___x_3_; 
lean_dec_ref(v_k_1_);
v___x_3_ = lean_box(0);
return v___x_3_;
}
else
{
lean_object* v_val_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_14_; 
v_val_4_ = lean_ctor_get(v_x_2_, 0);
v_isSharedCheck_14_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_14_ == 0)
{
v___x_6_ = v_x_2_;
v_isShared_7_ = v_isSharedCheck_14_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_val_4_);
lean_dec(v_x_2_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_14_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v___x_9_; 
if (v_isShared_7_ == 0)
{
lean_ctor_set_tag(v___x_6_, 3);
v___x_9_ = v___x_6_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v_val_4_);
v___x_9_ = v_reuseFailAlloc_13_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v_k_1_);
lean_ctor_set(v___x_10_, 1, v___x_9_);
v___x_11_ = lean_box(0);
v___x_12_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_12_, 0, v___x_10_);
lean_ctor_set(v___x_12_, 1, v___x_11_);
return v___x_12_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(lean_object* v_a_15_, lean_object* v_a_16_){
_start:
{
if (lean_obj_tag(v_a_15_) == 0)
{
lean_object* v___x_17_; 
v___x_17_ = lean_array_to_list(v_a_16_);
return v___x_17_;
}
else
{
lean_object* v_head_18_; lean_object* v_tail_19_; lean_object* v___x_20_; 
v_head_18_ = lean_ctor_get(v_a_15_, 0);
lean_inc(v_head_18_);
v_tail_19_ = lean_ctor_get(v_a_15_, 1);
lean_inc(v_tail_19_);
lean_dec_ref_known(v_a_15_, 2);
v___x_20_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_16_, v_head_18_);
v_a_15_ = v_tail_19_;
v_a_16_ = v___x_20_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonClientInfo_toJson(lean_object* v_x_26_){
_start:
{
lean_object* v_name_27_; lean_object* v_version_x3f_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_46_; 
v_name_27_ = lean_ctor_get(v_x_26_, 0);
v_version_x3f_28_ = lean_ctor_get(v_x_26_, 1);
v_isSharedCheck_46_ = !lean_is_exclusive(v_x_26_);
if (v_isSharedCheck_46_ == 0)
{
v___x_30_ = v_x_26_;
v_isShared_31_ = v_isSharedCheck_46_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_version_x3f_28_);
lean_inc(v_name_27_);
lean_dec(v_x_26_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_46_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_32_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0));
v___x_33_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_33_, 0, v_name_27_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 1, v___x_33_);
lean_ctor_set(v___x_30_, 0, v___x_32_);
v___x_35_ = v___x_30_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v___x_32_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v___x_33_);
v___x_35_ = v_reuseFailAlloc_45_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_36_ = lean_box(0);
v___x_37_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_35_);
lean_ctor_set(v___x_37_, 1, v___x_36_);
v___x_38_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1));
v___x_39_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__0(v___x_38_, v_version_x3f_28_);
v___x_40_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
lean_ctor_set(v___x_40_, 1, v___x_36_);
v___x_41_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_41_, 0, v___x_37_);
lean_ctor_set(v___x_41_, 1, v___x_40_);
v___x_42_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2));
v___x_43_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_41_, v___x_42_);
v___x_44_ = l_Lean_Json_mkObj(v___x_43_);
lean_dec(v___x_43_);
return v___x_44_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__0(lean_object* v_j_49_, lean_object* v_k_50_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = l_Lean_Json_getObjValD(v_j_49_, v_k_50_);
v___x_52_ = l_Lean_Json_getStr_x3f(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__0___boxed(lean_object* v_j_53_, lean_object* v_k_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__0(v_j_53_, v_k_54_);
lean_dec_ref(v_k_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1(lean_object* v_x_58_){
_start:
{
if (lean_obj_tag(v_x_58_) == 0)
{
lean_object* v___x_59_; 
v___x_59_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1___closed__0));
return v___x_59_;
}
else
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_Json_getStr_x3f(v_x_58_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_68_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_68_ == 0)
{
v___x_63_ = v___x_60_;
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_a_61_);
lean_dec(v___x_60_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_66_; 
if (v_isShared_64_ == 0)
{
v___x_66_ = v___x_63_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_a_61_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
else
{
lean_object* v_a_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_77_; 
v_a_69_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_77_ == 0)
{
v___x_71_ = v___x_60_;
v_isShared_72_ = v_isSharedCheck_77_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_a_69_);
lean_dec(v___x_60_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_77_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_73_; lean_object* v___x_75_; 
v___x_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_73_, 0, v_a_69_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v___x_73_);
v___x_75_ = v___x_71_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v___x_73_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
return v___x_75_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1(lean_object* v_j_78_, lean_object* v_k_79_){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = l_Lean_Json_getObjValD(v_j_78_, v_k_79_);
v___x_81_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1(v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1___boxed(lean_object* v_j_82_, lean_object* v_k_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1(v_j_82_, v_k_83_);
lean_dec_ref(v_k_83_);
return v_res_84_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__4(void){
_start:
{
uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = 1;
v___x_93_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3));
v___x_94_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_93_, v___x_92_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5));
v___x_97_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__4, &l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__4);
v___x_98_ = lean_string_append(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8(void){
_start:
{
uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = 1;
v___x_102_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__7));
v___x_103_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_102_, v___x_101_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__9(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8, &l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8);
v___x_105_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6, &l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6);
v___x_106_ = lean_string_append(v___x_105_, v___x_104_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__11(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_109_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__9, &l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__9);
v___x_110_ = lean_string_append(v___x_109_, v___x_108_);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14(void){
_start:
{
uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = 1;
v___x_115_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__13));
v___x_116_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_115_, v___x_114_);
return v___x_116_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__15(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14, &l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14);
v___x_118_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6, &l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6);
v___x_119_ = lean_string_append(v___x_118_, v___x_117_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__16(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_120_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_121_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__15, &l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__15);
v___x_122_ = lean_string_append(v___x_121_, v___x_120_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonClientInfo_fromJson(lean_object* v_json_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0));
lean_inc(v_json_123_);
v___x_125_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__0(v_json_123_, v___x_124_);
if (lean_obj_tag(v___x_125_) == 0)
{
lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_135_; 
lean_dec(v_json_123_);
v_a_126_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_135_ == 0)
{
v___x_128_ = v___x_125_;
v_isShared_129_ = v_isSharedCheck_135_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_dec(v___x_125_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_135_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_130_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__11, &l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__11);
v___x_131_ = lean_string_append(v___x_130_, v_a_126_);
lean_dec(v_a_126_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 0, v___x_131_);
v___x_133_ = v___x_128_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
else
{
if (lean_obj_tag(v___x_125_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
lean_dec(v_json_123_);
v_a_136_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___x_125_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_125_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
lean_ctor_set_tag(v___x_138_, 0);
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
else
{
lean_object* v_a_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v_a_144_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_a_144_);
lean_dec_ref_known(v___x_125_, 1);
v___x_145_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1));
v___x_146_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1(v_json_123_, v___x_145_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_156_; 
lean_dec(v_a_144_);
v_a_147_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_156_ == 0)
{
v___x_149_ = v___x_146_;
v_isShared_150_ = v_isSharedCheck_156_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_146_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_156_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_151_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__16, &l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__16);
v___x_152_ = lean_string_append(v___x_151_, v_a_147_);
lean_dec(v_a_147_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_152_);
v___x_154_ = v___x_149_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
else
{
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
lean_dec(v_a_144_);
v_a_157_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___x_146_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_146_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
lean_ctor_set_tag(v___x_159_, 0);
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
else
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_173_; 
v_a_165_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_173_ == 0)
{
v___x_167_ = v___x_146_;
v_isShared_168_ = v_isSharedCheck_173_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_146_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_173_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_169_, 0, v_a_144_);
lean_ctor_set(v___x_169_, 1, v_a_165_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_169_);
v___x_171_ = v___x_167_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorIdx(uint8_t v_x_176_){
_start:
{
switch(v_x_176_)
{
case 0:
{
lean_object* v___x_177_; 
v___x_177_ = lean_unsigned_to_nat(0u);
return v___x_177_;
}
case 1:
{
lean_object* v___x_178_; 
v___x_178_ = lean_unsigned_to_nat(1u);
return v___x_178_;
}
default: 
{
lean_object* v___x_179_; 
v___x_179_ = lean_unsigned_to_nat(2u);
return v___x_179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorIdx___boxed(lean_object* v_x_180_){
_start:
{
uint8_t v_x_boxed_181_; lean_object* v_res_182_; 
v_x_boxed_181_ = lean_unbox(v_x_180_);
v_res_182_ = l_Lean_Lsp_Trace_ctorIdx(v_x_boxed_181_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorElim___redArg(lean_object* v_k_183_){
_start:
{
lean_inc(v_k_183_);
return v_k_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorElim___redArg___boxed(lean_object* v_k_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_Lsp_Trace_ctorElim___redArg(v_k_184_);
lean_dec(v_k_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorElim(lean_object* v_motive_186_, lean_object* v_ctorIdx_187_, uint8_t v_t_188_, lean_object* v_h_189_, lean_object* v_k_190_){
_start:
{
lean_inc(v_k_190_);
return v_k_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorElim___boxed(lean_object* v_motive_191_, lean_object* v_ctorIdx_192_, lean_object* v_t_193_, lean_object* v_h_194_, lean_object* v_k_195_){
_start:
{
uint8_t v_t_boxed_196_; lean_object* v_res_197_; 
v_t_boxed_196_ = lean_unbox(v_t_193_);
v_res_197_ = l_Lean_Lsp_Trace_ctorElim(v_motive_191_, v_ctorIdx_192_, v_t_boxed_196_, v_h_194_, v_k_195_);
lean_dec(v_k_195_);
lean_dec(v_ctorIdx_192_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_off_elim___redArg(lean_object* v_off_198_){
_start:
{
lean_inc(v_off_198_);
return v_off_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_off_elim___redArg___boxed(lean_object* v_off_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Lsp_Trace_off_elim___redArg(v_off_199_);
lean_dec(v_off_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_off_elim(lean_object* v_motive_201_, uint8_t v_t_202_, lean_object* v_h_203_, lean_object* v_off_204_){
_start:
{
lean_inc(v_off_204_);
return v_off_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_off_elim___boxed(lean_object* v_motive_205_, lean_object* v_t_206_, lean_object* v_h_207_, lean_object* v_off_208_){
_start:
{
uint8_t v_t_boxed_209_; lean_object* v_res_210_; 
v_t_boxed_209_ = lean_unbox(v_t_206_);
v_res_210_ = l_Lean_Lsp_Trace_off_elim(v_motive_205_, v_t_boxed_209_, v_h_207_, v_off_208_);
lean_dec(v_off_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_messages_elim___redArg(lean_object* v_messages_211_){
_start:
{
lean_inc(v_messages_211_);
return v_messages_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_messages_elim___redArg___boxed(lean_object* v_messages_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_Lsp_Trace_messages_elim___redArg(v_messages_212_);
lean_dec(v_messages_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_messages_elim(lean_object* v_motive_214_, uint8_t v_t_215_, lean_object* v_h_216_, lean_object* v_messages_217_){
_start:
{
lean_inc(v_messages_217_);
return v_messages_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_messages_elim___boxed(lean_object* v_motive_218_, lean_object* v_t_219_, lean_object* v_h_220_, lean_object* v_messages_221_){
_start:
{
uint8_t v_t_boxed_222_; lean_object* v_res_223_; 
v_t_boxed_222_ = lean_unbox(v_t_219_);
v_res_223_ = l_Lean_Lsp_Trace_messages_elim(v_motive_218_, v_t_boxed_222_, v_h_220_, v_messages_221_);
lean_dec(v_messages_221_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_verbose_elim___redArg(lean_object* v_verbose_224_){
_start:
{
lean_inc(v_verbose_224_);
return v_verbose_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_verbose_elim___redArg___boxed(lean_object* v_verbose_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_Lsp_Trace_verbose_elim___redArg(v_verbose_225_);
lean_dec(v_verbose_225_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_verbose_elim(lean_object* v_motive_227_, uint8_t v_t_228_, lean_object* v_h_229_, lean_object* v_verbose_230_){
_start:
{
lean_inc(v_verbose_230_);
return v_verbose_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_verbose_elim___boxed(lean_object* v_motive_231_, lean_object* v_t_232_, lean_object* v_h_233_, lean_object* v_verbose_234_){
_start:
{
uint8_t v_t_boxed_235_; lean_object* v_res_236_; 
v_t_boxed_235_ = lean_unbox(v_t_232_);
v_res_236_ = l_Lean_Lsp_Trace_verbose_elim(v_motive_231_, v_t_boxed_235_, v_h_233_, v_verbose_234_);
lean_dec(v_verbose_234_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTrace___lam__0(lean_object* v_j_252_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_Json_getStr_x3f(v_j_252_);
if (lean_obj_tag(v___x_255_) == 1)
{
lean_object* v_a_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_256_);
lean_dec_ref_known(v___x_255_, 1);
v___x_257_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__2));
v___x_258_ = lean_string_dec_eq(v_a_256_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__3));
v___x_260_ = lean_string_dec_eq(v_a_256_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__4));
v___x_262_ = lean_string_dec_eq(v_a_256_, v___x_261_);
lean_dec(v_a_256_);
if (v___x_262_ == 0)
{
goto v___jp_253_;
}
else
{
lean_object* v___x_263_; 
v___x_263_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__5));
return v___x_263_;
}
}
else
{
lean_object* v___x_264_; 
lean_dec(v_a_256_);
v___x_264_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__6));
return v___x_264_;
}
}
else
{
lean_object* v___x_265_; 
lean_dec(v_a_256_);
v___x_265_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__7));
return v___x_265_;
}
}
else
{
lean_dec_ref(v___x_255_);
goto v___jp_253_;
}
v___jp_253_:
{
lean_object* v___x_254_; 
v___x_254_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__1));
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_hasToJson___lam__0(uint8_t v_x_274_){
_start:
{
switch(v_x_274_)
{
case 0:
{
lean_object* v___x_275_; 
v___x_275_ = ((lean_object*)(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__0));
return v___x_275_;
}
case 1:
{
lean_object* v___x_276_; 
v___x_276_ = ((lean_object*)(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__1));
return v___x_276_;
}
default: 
{
lean_object* v___x_277_; 
v___x_277_ = ((lean_object*)(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__2));
return v___x_277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_hasToJson___lam__0___boxed(lean_object* v_x_278_){
_start:
{
uint8_t v_x_54__boxed_279_; lean_object* v_res_280_; 
v_x_54__boxed_279_ = lean_unbox(v_x_278_);
v_res_280_ = l_Lean_Lsp_Trace_hasToJson___lam__0(v_x_54__boxed_279_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__0(lean_object* v_x1_283_, lean_object* v_x2_284_, lean_object* v_x3_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = lean_array_push(v_x1_283_, v_x2_284_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__1(lean_object* v_inst_287_, lean_object* v_x_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = lean_apply_1(v_inst_287_, v_x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__2(lean_object* v___f_309_, lean_object* v___f_310_, lean_object* v_s_311_){
_start:
{
lean_object* v_size_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; size_t v_sz_316_; size_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v_size_312_ = lean_ctor_get(v_s_311_, 0);
v___x_313_ = lean_mk_empty_array_with_capacity(v_size_312_);
v___x_314_ = ((lean_object*)(l_Lean_Lsp_instToJsonHashSet___redArg___lam__2___closed__9));
v___x_315_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_314_, v___f_309_, v___x_313_, v_s_311_);
v_sz_316_ = lean_array_size(v___x_315_);
v___x_317_ = ((size_t)0ULL);
v___x_318_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_314_, v___f_310_, v_sz_316_, v___x_317_, v___x_315_);
v___x_319_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg(lean_object* v_inst_321_){
_start:
{
lean_object* v___f_322_; lean_object* v___f_323_; lean_object* v___f_324_; 
v___f_322_ = ((lean_object*)(l_Lean_Lsp_instToJsonHashSet___redArg___closed__0));
v___f_323_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_323_, 0, v_inst_321_);
v___f_324_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonHashSet___redArg___lam__2), 3, 2);
lean_closure_set(v___f_324_, 0, v___f_322_);
lean_closure_set(v___f_324_, 1, v___f_323_);
return v___f_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet(lean_object* v_00_u03b1_325_, lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_inst_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_Lsp_instToJsonHashSet___redArg(v_inst_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___boxed(lean_object* v_00_u03b1_330_, lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_inst_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Lsp_instToJsonHashSet(v_00_u03b1_330_, v_inst_331_, v_inst_332_, v_inst_333_);
lean_dec_ref(v_inst_332_);
lean_dec_ref(v_inst_331_);
return v_res_334_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v_cellCount_339_; lean_object* v___x_340_; 
v_cellCount_339_ = lean_unsigned_to_nat(16u);
v___x_340_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_339_);
return v___x_340_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v_cellCount_341_; lean_object* v___x_342_; 
v_cellCount_341_ = lean_unsigned_to_nat(16u);
v___x_342_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_341_);
return v___x_342_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_343_ = lean_obj_once(&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3, &l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3_once, _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3);
v___x_344_ = lean_obj_once(&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2, &l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2_once, _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2);
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_344_);
lean_ctor_set(v___x_346_, 2, v___x_343_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0(lean_object* v___x_350_, lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v_inst_353_, lean_object* v_x_354_){
_start:
{
if (lean_obj_tag(v_x_354_) == 4)
{
lean_object* v_elems_355_; size_t v_sz_356_; size_t v___x_357_; lean_object* v___x_358_; 
v_elems_355_ = lean_ctor_get(v_x_354_, 0);
lean_inc_ref(v_elems_355_);
lean_dec_ref_known(v_x_354_, 1);
v_sz_356_ = lean_array_size(v_elems_355_);
v___x_357_ = ((size_t)0ULL);
v___x_358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_350_, v_inst_351_, v_sz_356_, v___x_357_, v_elems_355_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec_ref(v_inst_353_);
lean_dec_ref(v_inst_352_);
v_a_359_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_358_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
else
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_377_; 
v_a_367_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_377_ == 0)
{
v___x_369_ = v___x_358_;
v_isShared_370_ = v_isSharedCheck_377_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_358_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_377_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___f_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
v___f_371_ = ((lean_object*)(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__1));
v___x_372_ = lean_obj_once(&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__4, &l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__4_once, _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__4);
v___x_373_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_371_, v_inst_352_, v_inst_353_, v___x_372_, v_a_367_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_373_);
v___x_375_ = v___x_369_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
else
{
lean_object* v___x_378_; 
lean_dec(v_x_354_);
lean_dec_ref(v_inst_353_);
lean_dec_ref(v_inst_352_);
lean_dec_ref(v_inst_351_);
lean_dec_ref(v___x_350_);
v___x_378_ = ((lean_object*)(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__6));
return v___x_378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg(lean_object* v_inst_398_, lean_object* v_inst_399_, lean_object* v_inst_400_){
_start:
{
lean_object* v___x_401_; lean_object* v___f_402_; 
v___x_401_ = ((lean_object*)(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__9));
v___f_402_ = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0), 5, 4);
lean_closure_set(v___f_402_, 0, v___x_401_);
lean_closure_set(v___f_402_, 1, v_inst_400_);
lean_closure_set(v___f_402_, 2, v_inst_398_);
lean_closure_set(v___f_402_, 3, v_inst_399_);
return v___f_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHashSet(lean_object* v_00_u03b1_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_inst_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_Lsp_instFromJsonHashSet___redArg(v_inst_404_, v_inst_405_, v_inst_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0_spec__0(lean_object* v_x_408_){
_start:
{
if (lean_obj_tag(v_x_408_) == 0)
{
lean_object* v___x_409_; 
v___x_409_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1___closed__0));
return v___x_409_;
}
else
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_Json_getStr_x3f(v_x_408_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_410_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_410_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_427_; 
v_a_419_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_427_ == 0)
{
v___x_421_ = v___x_410_;
v_isShared_422_ = v_isSharedCheck_427_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_410_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_427_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_423_, 0, v_a_419_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_423_);
v___x_425_ = v___x_421_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0(lean_object* v_j_428_, lean_object* v_k_429_){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = l_Lean_Json_getObjValD(v_j_428_, v_k_429_);
v___x_431_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0_spec__0(v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0___boxed(lean_object* v_j_432_, lean_object* v_k_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0(v_j_432_, v_k_433_);
lean_dec_ref(v_k_433_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_m_435_, lean_object* v_query_436_, lean_object* v_x_437_, lean_object* v_x_438_, lean_object* v_x_439_){
_start:
{
lean_object* v_zero_440_; uint8_t v_isZero_441_; 
v_zero_440_ = lean_unsigned_to_nat(0u);
v_isZero_441_ = lean_nat_dec_eq(v_x_438_, v_zero_440_);
if (v_isZero_441_ == 1)
{
lean_dec(v_x_439_);
lean_dec(v_x_438_);
if (lean_obj_tag(v_x_437_) == 0)
{
lean_object* v___x_442_; 
v___x_442_ = lean_box(2);
return v___x_442_;
}
else
{
lean_object* v_val_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
v_val_443_ = lean_ctor_get(v_x_437_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v_x_437_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v_x_437_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_val_443_);
lean_dec(v_x_437_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_val_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
else
{
lean_object* v_keyArray_451_; lean_object* v_valueArray_452_; lean_object* v___x_453_; uint8_t v_isSome_454_; 
v_keyArray_451_ = lean_ctor_get(v_m_435_, 1);
v_valueArray_452_ = lean_ctor_get(v_m_435_, 2);
v___x_453_ = lean_array_fget_borrowed(v_keyArray_451_, v_x_439_);
v_isSome_454_ = lean_noption_is_some(v___x_453_);
if (v_isSome_454_ == 0)
{
lean_dec(v_x_438_);
if (lean_obj_tag(v_x_437_) == 0)
{
lean_object* v___x_455_; 
v___x_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_455_, 0, v_x_439_);
return v___x_455_;
}
else
{
lean_object* v_val_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
lean_dec(v_x_439_);
v_val_456_ = lean_ctor_get(v_x_437_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v_x_437_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v_x_437_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_val_456_);
lean_dec(v_x_437_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_val_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
else
{
lean_object* v_one_464_; lean_object* v_n_465_; lean_object* v___y_467_; 
v_one_464_ = lean_unsigned_to_nat(1u);
v_n_465_ = lean_nat_sub(v_x_438_, v_one_464_);
lean_dec(v_x_438_);
if (v_isSome_454_ == 0)
{
goto v___jp_473_;
}
else
{
lean_object* v___x_475_; uint8_t v_isSome_476_; 
v___x_475_ = lean_array_fget_borrowed(v_valueArray_452_, v_x_439_);
v_isSome_476_ = lean_noption_is_some(v___x_475_);
if (v_isSome_476_ == 0)
{
goto v___jp_473_;
}
else
{
lean_object* v_val_477_; uint8_t v___x_478_; 
lean_inc(v___x_453_);
v_val_477_ = lean_noption_get(v___x_453_);
v___x_478_ = lean_string_dec_eq(v_val_477_, v_query_436_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
lean_dec(v_val_477_);
v___x_479_ = lean_array_get_size(v_keyArray_451_);
v___x_480_ = lean_nat_add(v_x_439_, v_one_464_);
lean_dec(v_x_439_);
v___x_481_ = lean_nat_dec_lt(v___x_480_, v___x_479_);
if (v___x_481_ == 0)
{
lean_dec(v___x_480_);
v_x_438_ = v_n_465_;
v_x_439_ = v_zero_440_;
goto _start;
}
else
{
v_x_438_ = v_n_465_;
v_x_439_ = v___x_480_;
goto _start;
}
}
else
{
lean_object* v_val_484_; lean_object* v___x_485_; 
lean_dec(v_n_465_);
lean_dec(v_x_437_);
lean_inc(v___x_475_);
v_val_484_ = lean_noption_get(v___x_475_);
v___x_485_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_485_, 0, v_x_439_);
lean_ctor_set(v___x_485_, 1, v_val_477_);
lean_ctor_set(v___x_485_, 2, v_val_484_);
return v___x_485_;
}
}
}
v___jp_466_:
{
lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_468_ = lean_array_get_size(v_keyArray_451_);
v___x_469_ = lean_nat_add(v_x_439_, v_one_464_);
lean_dec(v_x_439_);
v___x_470_ = lean_nat_dec_lt(v___x_469_, v___x_468_);
if (v___x_470_ == 0)
{
lean_dec(v___x_469_);
v_x_437_ = v___y_467_;
v_x_438_ = v_n_465_;
v_x_439_ = v_zero_440_;
goto _start;
}
else
{
v_x_437_ = v___y_467_;
v_x_438_ = v_n_465_;
v_x_439_ = v___x_469_;
goto _start;
}
}
v___jp_473_:
{
if (lean_obj_tag(v_x_437_) == 0)
{
lean_object* v___x_474_; 
lean_inc(v_x_439_);
v___x_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_474_, 0, v_x_439_);
v___y_467_ = v___x_474_;
goto v___jp_466_;
}
else
{
v___y_467_ = v_x_437_;
goto v___jp_466_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_m_486_, lean_object* v_query_487_, lean_object* v_x_488_, lean_object* v_x_489_, lean_object* v_x_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_m_486_, v_query_487_, v_x_488_, v_x_489_, v_x_490_);
lean_dec_ref(v_query_487_);
lean_dec_ref(v_m_486_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_m_492_, lean_object* v_query_493_){
_start:
{
lean_object* v_keyArray_494_; lean_object* v___x_495_; uint64_t v___x_496_; uint64_t v___x_497_; uint64_t v___x_498_; uint64_t v_fold_499_; uint64_t v___x_500_; uint64_t v___x_501_; uint64_t v___x_502_; size_t v___x_503_; size_t v___x_504_; size_t v___x_505_; size_t v___x_506_; size_t v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v_keyArray_494_ = lean_ctor_get(v_m_492_, 1);
v___x_495_ = lean_array_get_size(v_keyArray_494_);
v___x_496_ = lean_string_hash(v_query_493_);
v___x_497_ = 32ULL;
v___x_498_ = lean_uint64_shift_right(v___x_496_, v___x_497_);
v_fold_499_ = lean_uint64_xor(v___x_496_, v___x_498_);
v___x_500_ = 16ULL;
v___x_501_ = lean_uint64_shift_right(v_fold_499_, v___x_500_);
v___x_502_ = lean_uint64_xor(v_fold_499_, v___x_501_);
v___x_503_ = lean_uint64_to_usize(v___x_502_);
v___x_504_ = lean_usize_of_nat(v___x_495_);
v___x_505_ = ((size_t)1ULL);
v___x_506_ = lean_usize_sub(v___x_504_, v___x_505_);
v___x_507_ = lean_usize_land(v___x_503_, v___x_506_);
v___x_508_ = lean_usize_to_nat(v___x_507_);
v___x_509_ = lean_box(0);
v___x_510_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_m_492_, v_query_493_, v___x_509_, v___x_495_, v___x_508_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_m_511_, lean_object* v_query_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(v_m_511_, v_query_512_);
lean_dec_ref(v_query_512_);
lean_dec_ref(v_m_511_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9___redArg(lean_object* v_b_514_, lean_object* v_acc_515_, lean_object* v_i_516_){
_start:
{
lean_object* v___y_518_; lean_object* v_keyArray_526_; lean_object* v_valueArray_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v_keyArray_526_ = lean_ctor_get(v_b_514_, 1);
v_valueArray_527_ = lean_ctor_get(v_b_514_, 2);
v___x_528_ = lean_array_get_size(v_keyArray_526_);
v___x_529_ = lean_nat_dec_lt(v_i_516_, v___x_528_);
if (v___x_529_ == 0)
{
lean_dec(v_i_516_);
return v_acc_515_;
}
else
{
lean_object* v___x_530_; uint8_t v_isSome_531_; 
v___x_530_ = lean_array_fget_borrowed(v_keyArray_526_, v_i_516_);
v_isSome_531_ = lean_noption_is_some(v___x_530_);
if (v_isSome_531_ == 0)
{
goto v___jp_522_;
}
else
{
lean_object* v___x_532_; uint8_t v_isSome_533_; 
v___x_532_ = lean_array_fget_borrowed(v_valueArray_527_, v_i_516_);
v_isSome_533_ = lean_noption_is_some(v___x_532_);
if (v_isSome_533_ == 0)
{
goto v___jp_522_;
}
else
{
lean_object* v_val_534_; lean_object* v_val_535_; lean_object* v_i_537_; lean_object* v___x_542_; 
lean_inc(v___x_530_);
v_val_534_ = lean_noption_get(v___x_530_);
lean_inc(v___x_532_);
v_val_535_ = lean_noption_get(v___x_532_);
v___x_542_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(v_acc_515_, v_val_534_);
switch(lean_obj_tag(v___x_542_))
{
case 0:
{
lean_object* v_index_543_; lean_object* v_size_544_; lean_object* v___x_545_; 
v_index_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_index_543_);
lean_dec_ref_known(v___x_542_, 3);
v_size_544_ = lean_ctor_get(v_acc_515_, 0);
lean_inc(v_size_544_);
v___x_545_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_515_, v_size_544_, v_index_543_, v_val_534_, v_val_535_);
lean_dec(v_index_543_);
v___y_518_ = v___x_545_;
goto v___jp_517_;
}
case 1:
{
lean_object* v_index_546_; 
v_index_546_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_index_546_);
lean_dec_ref_known(v___x_542_, 1);
v_i_537_ = v_index_546_;
goto v___jp_536_;
}
default: 
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_515_, v___x_547_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_index_549_; 
v_index_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_index_549_);
lean_dec_ref_known(v___x_548_, 1);
v_i_537_ = v_index_549_;
goto v___jp_536_;
}
else
{
lean_dec(v_val_535_);
lean_dec(v_val_534_);
v___y_518_ = v_acc_515_;
goto v___jp_517_;
}
}
}
v___jp_536_:
{
lean_object* v_size_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v_size_538_ = lean_ctor_get(v_acc_515_, 0);
v___x_539_ = lean_unsigned_to_nat(1u);
v___x_540_ = lean_nat_add(v_size_538_, v___x_539_);
v___x_541_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_515_, v___x_540_, v_i_537_, v_val_534_, v_val_535_);
lean_dec(v_i_537_);
v___y_518_ = v___x_541_;
goto v___jp_517_;
}
}
}
}
v___jp_517_:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_unsigned_to_nat(1u);
v___x_520_ = lean_nat_add(v_i_516_, v___x_519_);
lean_dec(v_i_516_);
v_acc_515_ = v___y_518_;
v_i_516_ = v___x_520_;
goto _start;
}
v___jp_522_:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_add(v_i_516_, v___x_523_);
lean_dec(v_i_516_);
v_i_516_ = v___x_524_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9___redArg___boxed(lean_object* v_b_550_, lean_object* v_acc_551_, lean_object* v_i_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9___redArg(v_b_550_, v_acc_551_, v_i_552_);
lean_dec_ref(v_b_550_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(lean_object* v_init_554_, lean_object* v_b_555_){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9___redArg(v_b_555_, v_init_554_, v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_init_558_, lean_object* v_b_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_init_558_, v_b_559_);
lean_dec_ref(v_b_559_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_m_561_){
_start:
{
lean_object* v_keyArray_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v_cellCount_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v_target_569_; lean_object* v___x_570_; 
v_keyArray_562_ = lean_ctor_get(v_m_561_, 1);
v___x_563_ = lean_array_get_size(v_keyArray_562_);
v___x_564_ = lean_unsigned_to_nat(2u);
v_cellCount_565_ = lean_nat_mul(v___x_563_, v___x_564_);
v___x_566_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_565_);
v___x_567_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_565_);
v___x_568_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_565_);
v_target_569_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_569_, 0, v___x_566_);
lean_ctor_set(v_target_569_, 1, v___x_567_);
lean_ctor_set(v_target_569_, 2, v___x_568_);
v___x_570_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_target_569_, v_m_561_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_m_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6___redArg(v_m_571_);
lean_dec_ref(v_m_571_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__7(lean_object* v_as_573_, size_t v_sz_574_, size_t v_i_575_, lean_object* v_b_576_){
_start:
{
lean_object* v___y_578_; uint8_t v___x_582_; 
v___x_582_ = lean_usize_dec_lt(v_i_575_, v_sz_574_);
if (v___x_582_ == 0)
{
return v_b_576_;
}
else
{
lean_object* v_a_583_; lean_object* v___x_584_; lean_object* v___y_586_; lean_object* v_i_587_; lean_object* v___y_593_; lean_object* v___y_603_; lean_object* v_i_604_; lean_object* v___x_619_; 
v_a_583_ = lean_array_uget_borrowed(v_as_573_, v_i_575_);
v___x_584_ = lean_box(0);
v___x_619_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(v_b_576_, v_a_583_);
switch(lean_obj_tag(v___x_619_))
{
case 0:
{
lean_dec_ref_known(v___x_619_, 3);
v___y_578_ = v_b_576_;
goto v___jp_577_;
}
case 1:
{
lean_object* v_index_620_; lean_object* v_size_621_; lean_object* v_keyArray_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v_index_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_index_620_);
lean_dec_ref_known(v___x_619_, 1);
v_size_621_ = lean_ctor_get(v_b_576_, 0);
v_keyArray_622_ = lean_ctor_get(v_b_576_, 1);
v___x_623_ = lean_unsigned_to_nat(1u);
v___x_624_ = lean_nat_add(v_size_621_, v___x_623_);
v___x_625_ = lean_array_get_size(v_keyArray_622_);
v___x_626_ = lean_nat_dec_lt(v___x_624_, v___x_625_);
if (v___x_626_ == 0)
{
lean_dec(v___x_624_);
lean_dec(v_index_620_);
goto v___jp_609_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_627_ = lean_unsigned_to_nat(4u);
v___x_628_ = lean_nat_mul(v___x_624_, v___x_627_);
v___x_629_ = lean_unsigned_to_nat(3u);
v___x_630_ = lean_nat_mul(v___x_625_, v___x_629_);
v___x_631_ = lean_nat_dec_le(v___x_628_, v___x_630_);
lean_dec(v___x_630_);
lean_dec(v___x_628_);
if (v___x_631_ == 0)
{
lean_dec(v___x_624_);
lean_dec(v_index_620_);
goto v___jp_609_;
}
else
{
lean_object* v___x_632_; 
lean_inc(v_a_583_);
v___x_632_ = l_Std_DHashMap_Raw_setEntry___redArg(v_b_576_, v___x_624_, v_index_620_, v_a_583_, v___x_584_);
lean_dec(v_index_620_);
v___y_578_ = v___x_632_;
goto v___jp_577_;
}
}
}
default: 
{
lean_object* v_size_633_; lean_object* v_keyArray_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v_size_633_ = lean_ctor_get(v_b_576_, 0);
v_keyArray_634_ = lean_ctor_get(v_b_576_, 1);
v___x_635_ = lean_unsigned_to_nat(1u);
v___x_636_ = lean_nat_add(v_size_633_, v___x_635_);
v___x_637_ = lean_array_get_size(v_keyArray_634_);
v___x_638_ = lean_nat_dec_lt(v___x_636_, v___x_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; 
lean_dec(v___x_636_);
v___x_639_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6___redArg(v_b_576_);
lean_dec_ref(v_b_576_);
v___y_593_ = v___x_639_;
goto v___jp_592_;
}
else
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_640_ = lean_unsigned_to_nat(4u);
v___x_641_ = lean_nat_mul(v___x_636_, v___x_640_);
lean_dec(v___x_636_);
v___x_642_ = lean_unsigned_to_nat(3u);
v___x_643_ = lean_nat_mul(v___x_637_, v___x_642_);
v___x_644_ = lean_nat_dec_le(v___x_641_, v___x_643_);
lean_dec(v___x_643_);
lean_dec(v___x_641_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
v___x_645_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6___redArg(v_b_576_);
lean_dec_ref(v_b_576_);
v___y_593_ = v___x_645_;
goto v___jp_592_;
}
else
{
v___y_593_ = v_b_576_;
goto v___jp_592_;
}
}
}
}
v___jp_585_:
{
lean_object* v_size_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v_size_588_ = lean_ctor_get(v___y_586_, 0);
v___x_589_ = lean_unsigned_to_nat(1u);
v___x_590_ = lean_nat_add(v_size_588_, v___x_589_);
lean_inc(v_a_583_);
v___x_591_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_586_, v___x_590_, v_i_587_, v_a_583_, v___x_584_);
lean_dec(v_i_587_);
v___y_578_ = v___x_591_;
goto v___jp_577_;
}
v___jp_592_:
{
lean_object* v___x_594_; 
v___x_594_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(v___y_593_, v_a_583_);
switch(lean_obj_tag(v___x_594_))
{
case 0:
{
lean_object* v_index_595_; lean_object* v_size_596_; lean_object* v___x_597_; 
v_index_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_index_595_);
lean_dec_ref_known(v___x_594_, 3);
v_size_596_ = lean_ctor_get(v___y_593_, 0);
lean_inc(v_size_596_);
lean_inc(v_a_583_);
v___x_597_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_593_, v_size_596_, v_index_595_, v_a_583_, v___x_584_);
lean_dec(v_index_595_);
v___y_578_ = v___x_597_;
goto v___jp_577_;
}
case 1:
{
lean_object* v_index_598_; 
v_index_598_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_index_598_);
lean_dec_ref_known(v___x_594_, 1);
v___y_586_ = v___y_593_;
v_i_587_ = v_index_598_;
goto v___jp_585_;
}
default: 
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_593_, v___x_599_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_index_601_; 
v_index_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_index_601_);
lean_dec_ref_known(v___x_600_, 1);
v___y_586_ = v___y_593_;
v_i_587_ = v_index_601_;
goto v___jp_585_;
}
else
{
v___y_578_ = v___y_593_;
goto v___jp_577_;
}
}
}
}
v___jp_602_:
{
lean_object* v_size_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v_size_605_ = lean_ctor_get(v___y_603_, 0);
v___x_606_ = lean_unsigned_to_nat(1u);
v___x_607_ = lean_nat_add(v_size_605_, v___x_606_);
lean_inc(v_a_583_);
v___x_608_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_603_, v___x_607_, v_i_604_, v_a_583_, v___x_584_);
lean_dec(v_i_604_);
v___y_578_ = v___x_608_;
goto v___jp_577_;
}
v___jp_609_:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6___redArg(v_b_576_);
lean_dec_ref(v_b_576_);
v___x_611_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(v___x_610_, v_a_583_);
switch(lean_obj_tag(v___x_611_))
{
case 0:
{
lean_object* v_index_612_; lean_object* v_size_613_; lean_object* v___x_614_; 
v_index_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_index_612_);
lean_dec_ref_known(v___x_611_, 3);
v_size_613_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_size_613_);
lean_inc(v_a_583_);
v___x_614_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_610_, v_size_613_, v_index_612_, v_a_583_, v___x_584_);
lean_dec(v_index_612_);
v___y_578_ = v___x_614_;
goto v___jp_577_;
}
case 1:
{
lean_object* v_index_615_; 
v_index_615_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_index_615_);
lean_dec_ref_known(v___x_611_, 1);
v___y_603_ = v___x_610_;
v_i_604_ = v_index_615_;
goto v___jp_602_;
}
default: 
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_unsigned_to_nat(0u);
v___x_617_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_610_, v___x_616_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_index_618_; 
v_index_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_index_618_);
lean_dec_ref_known(v___x_617_, 1);
v___y_603_ = v___x_610_;
v_i_604_ = v_index_618_;
goto v___jp_602_;
}
else
{
v___y_578_ = v___x_610_;
goto v___jp_577_;
}
}
}
}
}
v___jp_577_:
{
size_t v___x_579_; size_t v___x_580_; 
v___x_579_ = ((size_t)1ULL);
v___x_580_ = lean_usize_add(v_i_575_, v___x_579_);
v_i_575_ = v___x_580_;
v_b_576_ = v___y_578_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_as_646_, lean_object* v_sz_647_, lean_object* v_i_648_, lean_object* v_b_649_){
_start:
{
size_t v_sz_boxed_650_; size_t v_i_boxed_651_; lean_object* v_res_652_; 
v_sz_boxed_650_ = lean_unbox_usize(v_sz_647_);
lean_dec(v_sz_647_);
v_i_boxed_651_ = lean_unbox_usize(v_i_648_);
lean_dec(v_i_648_);
v_res_652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__7(v_as_646_, v_sz_boxed_650_, v_i_boxed_651_, v_b_649_);
lean_dec_ref(v_as_646_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4(lean_object* v_m_653_, lean_object* v_l_654_){
_start:
{
size_t v_sz_655_; size_t v___x_656_; lean_object* v___x_657_; 
v_sz_655_ = lean_array_size(v_l_654_);
v___x_656_ = ((size_t)0ULL);
v___x_657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__7(v_l_654_, v_sz_655_, v___x_656_, v_m_653_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4___boxed(lean_object* v_m_658_, lean_object* v_l_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4(v_m_658_, v_l_659_);
lean_dec_ref(v_l_659_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3(size_t v_sz_661_, size_t v_i_662_, lean_object* v_bs_663_){
_start:
{
uint8_t v___x_664_; 
v___x_664_ = lean_usize_dec_lt(v_i_662_, v_sz_661_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; 
v___x_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_665_, 0, v_bs_663_);
return v___x_665_;
}
else
{
lean_object* v_v_666_; lean_object* v___x_667_; 
v_v_666_ = lean_array_uget_borrowed(v_bs_663_, v_i_662_);
lean_inc(v_v_666_);
v___x_667_ = l_Lean_Json_getStr_x3f(v_v_666_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
lean_dec_ref(v_bs_663_);
v_a_668_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_667_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_677_; lean_object* v_bs_x27_678_; size_t v___x_679_; size_t v___x_680_; lean_object* v___x_681_; 
v_a_676_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_a_676_);
lean_dec_ref_known(v___x_667_, 1);
v___x_677_ = lean_unsigned_to_nat(0u);
v_bs_x27_678_ = lean_array_uset(v_bs_663_, v_i_662_, v___x_677_);
v___x_679_ = ((size_t)1ULL);
v___x_680_ = lean_usize_add(v_i_662_, v___x_679_);
v___x_681_ = lean_array_uset(v_bs_x27_678_, v_i_662_, v_a_676_);
v_i_662_ = v___x_680_;
v_bs_663_ = v___x_681_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3___boxed(lean_object* v_sz_683_, lean_object* v_i_684_, lean_object* v_bs_685_){
_start:
{
size_t v_sz_boxed_686_; size_t v_i_boxed_687_; lean_object* v_res_688_; 
v_sz_boxed_686_ = lean_unbox_usize(v_sz_683_);
lean_dec(v_sz_683_);
v_i_boxed_687_ = lean_unbox_usize(v_i_684_);
lean_dec(v_i_684_);
v_res_688_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3(v_sz_boxed_686_, v_i_boxed_687_, v_bs_685_);
return v_res_688_;
}
}
static lean_object* _init_l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v_cellCount_691_; lean_object* v___x_692_; 
v_cellCount_691_ = lean_unsigned_to_nat(16u);
v___x_692_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_691_);
return v___x_692_;
}
}
static lean_object* _init_l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_693_ = lean_obj_once(&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3, &l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3_once, _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3);
v___x_694_ = lean_obj_once(&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1, &l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1_once, _init_l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1);
v___x_695_ = lean_unsigned_to_nat(0u);
v___x_696_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v___x_694_);
lean_ctor_set(v___x_696_, 2, v___x_693_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2(lean_object* v_x_699_){
_start:
{
if (lean_obj_tag(v_x_699_) == 0)
{
lean_object* v___x_700_; 
v___x_700_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__0));
return v___x_700_;
}
else
{
if (lean_obj_tag(v_x_699_) == 4)
{
lean_object* v_elems_701_; size_t v_sz_702_; size_t v___x_703_; lean_object* v___x_704_; 
v_elems_701_ = lean_ctor_get(v_x_699_, 0);
lean_inc_ref(v_elems_701_);
lean_dec_ref_known(v_x_699_, 1);
v_sz_702_ = lean_array_size(v_elems_701_);
v___x_703_ = ((size_t)0ULL);
v___x_704_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3(v_sz_702_, v___x_703_, v_elems_701_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_704_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_704_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_723_; 
v_a_713_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_723_ == 0)
{
v___x_715_ = v___x_704_;
v_isShared_716_ = v_isSharedCheck_723_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_704_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_723_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_717_ = lean_obj_once(&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2, &l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2_once, _init_l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2);
v___x_718_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4(v___x_717_, v_a_713_);
lean_dec(v_a_713_);
v___x_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_719_);
v___x_721_ = v___x_715_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
else
{
lean_object* v___x_724_; 
lean_dec(v_x_699_);
v___x_724_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__3));
return v___x_724_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(lean_object* v_j_725_, lean_object* v_k_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = l_Lean_Json_getObjValD(v_j_725_, v_k_726_);
v___x_728_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2(v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1___boxed(lean_object* v_j_729_, lean_object* v_k_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(v_j_729_, v_k_730_);
lean_dec_ref(v_k_730_);
return v_res_731_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3(void){
_start:
{
uint8_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = 1;
v___x_739_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2));
v___x_740_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_739_, v___x_738_);
return v___x_740_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_741_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5));
v___x_742_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3);
v___x_743_ = lean_string_append(v___x_742_, v___x_741_);
return v___x_743_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7(void){
_start:
{
uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_747_ = 1;
v___x_748_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__6));
v___x_749_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_748_, v___x_747_);
return v___x_749_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_750_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7);
v___x_751_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4);
v___x_752_ = lean_string_append(v___x_751_, v___x_750_);
return v___x_752_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_754_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8);
v___x_755_ = lean_string_append(v___x_754_, v___x_753_);
return v___x_755_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13(void){
_start:
{
uint8_t v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_760_ = 1;
v___x_761_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__12));
v___x_762_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_761_, v___x_760_);
return v___x_762_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13);
v___x_764_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4);
v___x_765_ = lean_string_append(v___x_764_, v___x_763_);
return v___x_765_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_767_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14);
v___x_768_ = lean_string_append(v___x_767_, v___x_766_);
return v___x_768_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19(void){
_start:
{
uint8_t v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_773_ = 1;
v___x_774_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__18));
v___x_775_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_774_, v___x_773_);
return v___x_775_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19);
v___x_777_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4);
v___x_778_ = lean_string_append(v___x_777_, v___x_776_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_779_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_780_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20);
v___x_781_ = lean_string_append(v___x_780_, v___x_779_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson(lean_object* v_json_782_){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__0));
lean_inc(v_json_782_);
v___x_784_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0(v_json_782_, v___x_783_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_794_; 
lean_dec(v_json_782_);
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_794_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_794_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_794_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_789_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9);
v___x_790_ = lean_string_append(v___x_789_, v_a_785_);
lean_dec(v_a_785_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_790_);
v___x_792_ = v___x_787_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
else
{
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec(v_json_782_);
v_a_795_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_784_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_784_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
lean_ctor_set_tag(v___x_797_, 0);
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
else
{
lean_object* v_a_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_a_803_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_803_);
lean_dec_ref_known(v___x_784_, 1);
v___x_804_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__10));
lean_inc(v_json_782_);
v___x_805_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(v_json_782_, v___x_804_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_815_; 
lean_dec(v_a_803_);
lean_dec(v_json_782_);
v_a_806_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_815_ == 0)
{
v___x_808_ = v___x_805_;
v_isShared_809_ = v_isSharedCheck_815_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_805_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_815_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_810_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15);
v___x_811_ = lean_string_append(v___x_810_, v_a_806_);
lean_dec(v_a_806_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_811_);
v___x_813_ = v___x_808_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
else
{
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec(v_a_803_);
lean_dec(v_json_782_);
v_a_816_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_805_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_805_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
lean_ctor_set_tag(v___x_818_, 0);
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v_a_824_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_824_);
lean_dec_ref_known(v___x_805_, 1);
v___x_825_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__16));
v___x_826_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(v_json_782_, v___x_825_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_836_; 
lean_dec(v_a_824_);
lean_dec(v_a_803_);
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_836_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_836_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_836_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_831_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21);
v___x_832_ = lean_string_append(v___x_831_, v_a_827_);
lean_dec(v_a_827_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_832_);
v___x_834_ = v___x_829_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
else
{
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec(v_a_824_);
lean_dec(v_a_803_);
v_a_837_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_826_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_826_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
lean_ctor_set_tag(v___x_839_, 0);
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_853_; 
v_a_845_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_853_ == 0)
{
v___x_847_ = v___x_826_;
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_826_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_849_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_849_, 0, v_a_803_);
lean_ctor_set(v___x_849_, 1, v_a_824_);
lean_ctor_set(v___x_849_, 2, v_a_845_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_849_);
v___x_851_ = v___x_847_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_854_, lean_object* v_m_855_, lean_object* v_query_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(v_m_855_, v_query_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_858_, lean_object* v_m_859_, lean_object* v_query_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5(v_00_u03b2_858_, v_m_859_, v_query_860_);
lean_dec_ref(v_query_860_);
lean_dec_ref(v_m_859_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_862_, lean_object* v_m_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6___redArg(v_m_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_865_, lean_object* v_m_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_865_, v_m_866_);
lean_dec_ref(v_m_866_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_868_, lean_object* v_m_869_, lean_object* v_query_870_, lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_x_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_m_869_, v_query_870_, v_x_871_, v_x_872_, v_x_873_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_00_u03b2_876_, lean_object* v_m_877_, lean_object* v_query_878_, lean_object* v_x_879_, lean_object* v_x_880_, lean_object* v_x_881_, lean_object* v_x_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6(v_00_u03b2_876_, v_m_877_, v_query_878_, v_x_879_, v_x_880_, v_x_881_, v_x_882_);
lean_dec_ref(v_query_878_);
lean_dec_ref(v_m_877_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8(lean_object* v_00_u03b2_884_, lean_object* v_init_885_, lean_object* v_b_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_init_885_, v_b_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b2_888_, lean_object* v_init_889_, lean_object* v_b_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8(v_00_u03b2_888_, v_init_889_, v_b_890_);
lean_dec_ref(v_b_890_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(lean_object* v_00_u03b2_892_, lean_object* v_b_893_, lean_object* v_acc_894_, lean_object* v_i_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9___redArg(v_b_893_, v_acc_894_, v_i_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9___boxed(lean_object* v_00_u03b2_897_, lean_object* v_b_898_, lean_object* v_acc_899_, lean_object* v_i_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_00_u03b2_897_, v_b_898_, v_acc_899_, v_i_900_);
lean_dec_ref(v_b_898_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__0(lean_object* v_k_904_, lean_object* v_x_905_){
_start:
{
if (lean_obj_tag(v_x_905_) == 0)
{
lean_object* v___x_906_; 
lean_dec_ref(v_k_904_);
v___x_906_ = lean_box(0);
return v___x_906_;
}
else
{
lean_object* v_val_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_917_; 
v_val_907_ = lean_ctor_get(v_x_905_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v_x_905_);
if (v_isSharedCheck_917_ == 0)
{
v___x_909_ = v_x_905_;
v_isShared_910_ = v_isSharedCheck_917_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_val_907_);
lean_dec(v_x_905_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_917_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set_tag(v___x_909_, 3);
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_val_907_);
v___x_912_ = v_reuseFailAlloc_916_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_913_, 0, v_k_904_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_box(0);
v___x_915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
return v___x_915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1_spec__2(lean_object* v_b_918_, lean_object* v_acc_919_, lean_object* v_i_920_){
_start:
{
lean_object* v_keyArray_925_; lean_object* v_valueArray_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v_keyArray_925_ = lean_ctor_get(v_b_918_, 1);
v_valueArray_926_ = lean_ctor_get(v_b_918_, 2);
v___x_927_ = lean_array_get_size(v_keyArray_925_);
v___x_928_ = lean_nat_dec_lt(v_i_920_, v___x_927_);
if (v___x_928_ == 0)
{
lean_dec(v_i_920_);
return v_acc_919_;
}
else
{
lean_object* v___x_929_; uint8_t v_isSome_930_; 
v___x_929_ = lean_array_fget_borrowed(v_keyArray_925_, v_i_920_);
v_isSome_930_ = lean_noption_is_some(v___x_929_);
if (v_isSome_930_ == 0)
{
goto v___jp_921_;
}
else
{
lean_object* v___x_931_; uint8_t v_isSome_932_; 
v___x_931_ = lean_array_fget_borrowed(v_valueArray_926_, v_i_920_);
v_isSome_932_ = lean_noption_is_some(v___x_931_);
if (v_isSome_932_ == 0)
{
goto v___jp_921_;
}
else
{
lean_object* v_val_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
lean_inc(v___x_929_);
v_val_933_ = lean_noption_get(v___x_929_);
v___x_934_ = lean_array_push(v_acc_919_, v_val_933_);
v___x_935_ = lean_unsigned_to_nat(1u);
v___x_936_ = lean_nat_add(v_i_920_, v___x_935_);
lean_dec(v_i_920_);
v_acc_919_ = v___x_934_;
v_i_920_ = v___x_936_;
goto _start;
}
}
}
v___jp_921_:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_unsigned_to_nat(1u);
v___x_923_ = lean_nat_add(v_i_920_, v___x_922_);
lean_dec(v_i_920_);
v_i_920_ = v___x_923_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1_spec__2___boxed(lean_object* v_b_938_, lean_object* v_acc_939_, lean_object* v_i_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1_spec__2(v_b_938_, v_acc_939_, v_i_940_);
lean_dec_ref(v_b_938_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1(lean_object* v_init_942_, lean_object* v_b_943_){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = lean_unsigned_to_nat(0u);
v___x_945_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1_spec__2(v_b_943_, v_init_942_, v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1___boxed(lean_object* v_init_946_, lean_object* v_b_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1(v_init_946_, v_b_947_);
lean_dec_ref(v_b_947_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__2(size_t v_sz_949_, size_t v_i_950_, lean_object* v_bs_951_){
_start:
{
uint8_t v___x_952_; 
v___x_952_ = lean_usize_dec_lt(v_i_950_, v_sz_949_);
if (v___x_952_ == 0)
{
return v_bs_951_;
}
else
{
lean_object* v_v_953_; lean_object* v___x_954_; lean_object* v_bs_x27_955_; lean_object* v___x_956_; size_t v___x_957_; size_t v___x_958_; lean_object* v___x_959_; 
v_v_953_ = lean_array_uget(v_bs_951_, v_i_950_);
v___x_954_ = lean_unsigned_to_nat(0u);
v_bs_x27_955_ = lean_array_uset(v_bs_951_, v_i_950_, v___x_954_);
v___x_956_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_956_, 0, v_v_953_);
v___x_957_ = ((size_t)1ULL);
v___x_958_ = lean_usize_add(v_i_950_, v___x_957_);
v___x_959_ = lean_array_uset(v_bs_x27_955_, v_i_950_, v___x_956_);
v_i_950_ = v___x_958_;
v_bs_951_ = v___x_959_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__2___boxed(lean_object* v_sz_961_, lean_object* v_i_962_, lean_object* v_bs_963_){
_start:
{
size_t v_sz_boxed_964_; size_t v_i_boxed_965_; lean_object* v_res_966_; 
v_sz_boxed_964_ = lean_unbox_usize(v_sz_961_);
lean_dec(v_sz_961_);
v_i_boxed_965_ = lean_unbox_usize(v_i_962_);
lean_dec(v_i_962_);
v_res_966_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__2(v_sz_boxed_964_, v_i_boxed_965_, v_bs_963_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(lean_object* v_k_967_, lean_object* v_x_968_){
_start:
{
if (lean_obj_tag(v_x_968_) == 0)
{
lean_object* v___x_969_; 
lean_dec_ref(v_k_967_);
v___x_969_ = lean_box(0);
return v___x_969_;
}
else
{
lean_object* v_val_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_986_; 
v_val_970_ = lean_ctor_get(v_x_968_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v_x_968_);
if (v_isSharedCheck_986_ == 0)
{
v___x_972_ = v_x_968_;
v_isShared_973_ = v_isSharedCheck_986_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_val_970_);
lean_dec(v_x_968_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_986_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v_size_974_; lean_object* v___x_975_; lean_object* v___x_976_; size_t v_sz_977_; size_t v___x_978_; lean_object* v___x_979_; lean_object* v___x_981_; 
v_size_974_ = lean_ctor_get(v_val_970_, 0);
v___x_975_ = lean_mk_empty_array_with_capacity(v_size_974_);
v___x_976_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1(v___x_975_, v_val_970_);
lean_dec(v_val_970_);
v_sz_977_ = lean_array_size(v___x_976_);
v___x_978_ = ((size_t)0ULL);
v___x_979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__2(v_sz_977_, v___x_978_, v___x_976_);
if (v_isShared_973_ == 0)
{
lean_ctor_set_tag(v___x_972_, 4);
lean_ctor_set(v___x_972_, 0, v___x_979_);
v___x_981_ = v___x_972_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_979_);
v___x_981_ = v_reuseFailAlloc_985_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_982_, 0, v_k_967_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = lean_box(0);
v___x_984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
return v___x_984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLogConfig_toJson(lean_object* v_x_987_){
_start:
{
lean_object* v_logDir_x3f_988_; lean_object* v_allowedMethods_x3f_989_; lean_object* v_disallowedMethods_x3f_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_logDir_x3f_988_ = lean_ctor_get(v_x_987_, 0);
lean_inc(v_logDir_x3f_988_);
v_allowedMethods_x3f_989_ = lean_ctor_get(v_x_987_, 1);
lean_inc(v_allowedMethods_x3f_989_);
v_disallowedMethods_x3f_990_ = lean_ctor_get(v_x_987_, 2);
lean_inc(v_disallowedMethods_x3f_990_);
lean_dec_ref(v_x_987_);
v___x_991_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__0));
v___x_992_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__0(v___x_991_, v_logDir_x3f_988_);
v___x_993_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__10));
v___x_994_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(v___x_993_, v_allowedMethods_x3f_989_);
v___x_995_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__16));
v___x_996_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(v___x_995_, v_disallowedMethods_x3f_990_);
v___x_997_ = lean_box(0);
v___x_998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_994_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_992_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2));
v___x_1002_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_1000_, v___x_1001_);
v___x_1003_ = l_Lean_Json_mkObj(v___x_1002_);
lean_dec(v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0(lean_object* v_k_1006_, lean_object* v_x_1007_){
_start:
{
if (lean_obj_tag(v_x_1007_) == 0)
{
lean_object* v___x_1008_; 
lean_dec_ref(v_k_1006_);
v___x_1008_ = lean_box(0);
return v___x_1008_;
}
else
{
lean_object* v_val_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_val_1009_ = lean_ctor_get(v_x_1007_, 0);
v___x_1010_ = lean_alloc_ctor(1, 0, 1);
v___x_1011_ = lean_unbox(v_val_1009_);
lean_ctor_set_uint8(v___x_1010_, 0, v___x_1011_);
v___x_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1012_, 0, v_k_1006_);
lean_ctor_set(v___x_1012_, 1, v___x_1010_);
v___x_1013_ = lean_box(0);
v___x_1014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
return v___x_1014_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0___boxed(lean_object* v_k_1015_, lean_object* v_x_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0(v_k_1015_, v_x_1016_);
lean_dec(v_x_1016_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__1(lean_object* v_k_1018_, lean_object* v_x_1019_){
_start:
{
if (lean_obj_tag(v_x_1019_) == 0)
{
lean_object* v___x_1020_; 
lean_dec_ref(v_k_1018_);
v___x_1020_ = lean_box(0);
return v___x_1020_;
}
else
{
lean_object* v_val_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v_val_1021_ = lean_ctor_get(v_x_1019_, 0);
lean_inc(v_val_1021_);
lean_dec_ref_known(v_x_1019_, 1);
v___x_1022_ = l_Lean_Lsp_instToJsonLogConfig_toJson(v_val_1021_);
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v_k_1018_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = lean_box(0);
v___x_1025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1023_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
return v___x_1025_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonInitializationOptions_toJson(lean_object* v_x_1028_){
_start:
{
lean_object* v_hasWidgets_x3f_1029_; lean_object* v_logCfg_x3f_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1046_; 
v_hasWidgets_x3f_1029_ = lean_ctor_get(v_x_1028_, 0);
v_logCfg_x3f_1030_ = lean_ctor_get(v_x_1028_, 1);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_x_1028_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1032_ = v_x_1028_;
v_isShared_1033_ = v_isSharedCheck_1046_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_logCfg_x3f_1030_);
lean_inc(v_hasWidgets_x3f_1029_);
lean_dec(v_x_1028_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1046_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1034_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__0));
v___x_1035_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0(v___x_1034_, v_hasWidgets_x3f_1029_);
lean_dec(v_hasWidgets_x3f_1029_);
v___x_1036_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__1));
v___x_1037_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__1(v___x_1036_, v_logCfg_x3f_1030_);
v___x_1038_ = lean_box(0);
if (v_isShared_1033_ == 0)
{
lean_ctor_set_tag(v___x_1032_, 1);
lean_ctor_set(v___x_1032_, 1, v___x_1038_);
lean_ctor_set(v___x_1032_, 0, v___x_1037_);
v___x_1040_ = v___x_1032_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1035_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2));
v___x_1043_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_1041_, v___x_1042_);
v___x_1044_ = l_Lean_Json_mkObj(v___x_1043_);
lean_dec(v___x_1043_);
return v___x_1044_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2(lean_object* v_x_1051_){
_start:
{
if (lean_obj_tag(v_x_1051_) == 0)
{
lean_object* v___x_1052_; 
v___x_1052_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2___closed__0));
return v___x_1052_;
}
else
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_Lsp_instFromJsonLogConfig_fromJson(v_x_1051_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1053_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1053_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1070_; 
v_a_1062_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1064_ = v___x_1053_;
v_isShared_1065_ = v_isSharedCheck_1070_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1053_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1070_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1066_, 0, v_a_1062_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1066_);
v___x_1068_ = v___x_1064_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1(lean_object* v_j_1071_, lean_object* v_k_1072_){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = l_Lean_Json_getObjValD(v_j_1071_, v_k_1072_);
v___x_1074_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2(v___x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1___boxed(lean_object* v_j_1075_, lean_object* v_k_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1(v_j_1075_, v_k_1076_);
lean_dec_ref(v_k_1076_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0(lean_object* v_x_1080_){
_start:
{
if (lean_obj_tag(v_x_1080_) == 0)
{
lean_object* v___x_1081_; 
v___x_1081_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___closed__0));
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_Json_getBool_x3f(v_x_1080_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1099_; 
v_a_1091_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1093_ = v___x_1082_;
v_isShared_1094_ = v_isSharedCheck_1099_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1082_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1099_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1095_, 0, v_a_1091_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v___x_1095_);
v___x_1097_ = v___x_1093_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___boxed(lean_object* v_x_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0(v_x_1100_);
lean_dec(v_x_1100_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0(lean_object* v_j_1102_, lean_object* v_k_1103_){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = l_Lean_Json_getObjValD(v_j_1102_, v_k_1103_);
v___x_1105_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0(v___x_1104_);
lean_dec(v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0___boxed(lean_object* v_j_1106_, lean_object* v_k_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0(v_j_1106_, v_k_1107_);
lean_dec_ref(v_k_1107_);
return v_res_1108_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1114_ = 1;
v___x_1115_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1));
v___x_1116_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1115_, v___x_1114_);
return v___x_1116_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5));
v___x_1118_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2);
v___x_1119_ = lean_string_append(v___x_1118_, v___x_1117_);
return v___x_1119_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = 1;
v___x_1124_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__5));
v___x_1125_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1124_, v___x_1123_);
return v___x_1125_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6);
v___x_1127_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3);
v___x_1128_ = lean_string_append(v___x_1127_, v___x_1126_);
return v___x_1128_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1129_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_1130_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7);
v___x_1131_ = lean_string_append(v___x_1130_, v___x_1129_);
return v___x_1131_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11(void){
_start:
{
uint8_t v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = 1;
v___x_1136_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__10));
v___x_1137_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1136_, v___x_1135_);
return v___x_1137_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11);
v___x_1139_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3);
v___x_1140_ = lean_string_append(v___x_1139_, v___x_1138_);
return v___x_1140_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_1142_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12);
v___x_1143_ = lean_string_append(v___x_1142_, v___x_1141_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializationOptions_fromJson(lean_object* v_json_1144_){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__0));
lean_inc(v_json_1144_);
v___x_1146_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0(v_json_1144_, v___x_1145_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1156_; 
lean_dec(v_json_1144_);
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1156_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1156_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1151_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8);
v___x_1152_ = lean_string_append(v___x_1151_, v_a_1147_);
lean_dec(v_a_1147_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1152_);
v___x_1154_ = v___x_1149_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
else
{
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_dec(v_json_1144_);
v_a_1157_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1146_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1146_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set_tag(v___x_1159_, 0);
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v_a_1165_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1165_);
lean_dec_ref_known(v___x_1146_, 1);
v___x_1166_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__1));
v___x_1167_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1(v_json_1144_, v___x_1166_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1177_; 
lean_dec(v_a_1165_);
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1170_ = v___x_1167_;
v_isShared_1171_ = v_isSharedCheck_1177_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1167_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1177_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1172_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13);
v___x_1173_ = lean_string_append(v___x_1172_, v_a_1168_);
lean_dec(v_a_1168_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___x_1173_);
v___x_1175_ = v___x_1170_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
else
{
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec(v_a_1165_);
v_a_1178_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1167_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1167_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set_tag(v___x_1180_, 0);
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1194_; 
v_a_1186_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1188_ = v___x_1167_;
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1167_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1190_, 0, v_a_1165_);
lean_ctor_set(v___x_1190_, 1, v_a_1186_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1190_);
v___x_1192_ = v___x_1188_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__0(lean_object* v_k_1197_, lean_object* v_x_1198_){
_start:
{
if (lean_obj_tag(v_x_1198_) == 0)
{
lean_object* v___x_1199_; 
lean_dec_ref(v_k_1197_);
v___x_1199_ = lean_box(0);
return v___x_1199_;
}
else
{
lean_object* v_val_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1211_; 
v_val_1200_ = lean_ctor_get(v_x_1198_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_x_1198_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1202_ = v_x_1198_;
v_isShared_1203_ = v_isSharedCheck_1211_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_val_1200_);
lean_dec(v_x_1198_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1211_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1204_ = l_Lean_JsonNumber_fromInt(v_val_1200_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set_tag(v___x_1202_, 2);
lean_ctor_set(v___x_1202_, 0, v___x_1204_);
v___x_1206_ = v___x_1202_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1207_, 0, v_k_1197_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = lean_box(0);
v___x_1209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1207_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
return v___x_1209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__1(lean_object* v_k_1212_, lean_object* v_x_1213_){
_start:
{
if (lean_obj_tag(v_x_1213_) == 0)
{
lean_object* v___x_1214_; 
lean_dec_ref(v_k_1212_);
v___x_1214_ = lean_box(0);
return v___x_1214_;
}
else
{
lean_object* v_val_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v_val_1215_ = lean_ctor_get(v_x_1213_, 0);
lean_inc(v_val_1215_);
lean_dec_ref_known(v_x_1213_, 1);
v___x_1216_ = l_Lean_Lsp_instToJsonClientInfo_toJson(v_val_1215_);
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v_k_1212_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = lean_box(0);
v___x_1219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
return v___x_1219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__2(lean_object* v_k_1220_, lean_object* v_x_1221_){
_start:
{
if (lean_obj_tag(v_x_1221_) == 0)
{
lean_object* v___x_1222_; 
lean_dec_ref(v_k_1220_);
v___x_1222_ = lean_box(0);
return v___x_1222_;
}
else
{
lean_object* v_val_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v_val_1223_ = lean_ctor_get(v_x_1221_, 0);
lean_inc(v_val_1223_);
lean_dec_ref_known(v_x_1221_, 1);
v___x_1224_ = l_Lean_Lsp_instToJsonInitializationOptions_toJson(v_val_1223_);
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v_k_1220_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
v___x_1226_ = lean_box(0);
v___x_1227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1225_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
return v___x_1227_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4(size_t v_sz_1228_, size_t v_i_1229_, lean_object* v_bs_1230_){
_start:
{
uint8_t v___x_1231_; 
v___x_1231_ = lean_usize_dec_lt(v_i_1229_, v_sz_1228_);
if (v___x_1231_ == 0)
{
return v_bs_1230_;
}
else
{
lean_object* v_v_1232_; lean_object* v___x_1233_; lean_object* v_bs_x27_1234_; lean_object* v___x_1235_; size_t v___x_1236_; size_t v___x_1237_; lean_object* v___x_1238_; 
v_v_1232_ = lean_array_uget(v_bs_1230_, v_i_1229_);
v___x_1233_ = lean_unsigned_to_nat(0u);
v_bs_x27_1234_ = lean_array_uset(v_bs_1230_, v_i_1229_, v___x_1233_);
v___x_1235_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson(v_v_1232_);
v___x_1236_ = ((size_t)1ULL);
v___x_1237_ = lean_usize_add(v_i_1229_, v___x_1236_);
v___x_1238_ = lean_array_uset(v_bs_x27_1234_, v_i_1229_, v___x_1235_);
v_i_1229_ = v___x_1237_;
v_bs_1230_ = v___x_1238_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_1240_, lean_object* v_i_1241_, lean_object* v_bs_1242_){
_start:
{
size_t v_sz_boxed_1243_; size_t v_i_boxed_1244_; lean_object* v_res_1245_; 
v_sz_boxed_1243_ = lean_unbox_usize(v_sz_1240_);
lean_dec(v_sz_1240_);
v_i_boxed_1244_ = lean_unbox_usize(v_i_1241_);
lean_dec(v_i_1241_);
v_res_1245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4(v_sz_boxed_1243_, v_i_boxed_1244_, v_bs_1242_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3(lean_object* v_a_1246_){
_start:
{
size_t v_sz_1247_; size_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_sz_1247_ = lean_array_size(v_a_1246_);
v___x_1248_ = ((size_t)0ULL);
v___x_1249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4(v_sz_1247_, v___x_1248_, v_a_1246_);
v___x_1250_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3(lean_object* v_k_1251_, lean_object* v_x_1252_){
_start:
{
if (lean_obj_tag(v_x_1252_) == 0)
{
lean_object* v___x_1253_; 
lean_dec_ref(v_k_1251_);
v___x_1253_ = lean_box(0);
return v___x_1253_;
}
else
{
lean_object* v_val_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v_val_1254_ = lean_ctor_get(v_x_1252_, 0);
lean_inc(v_val_1254_);
lean_dec_ref_known(v_x_1252_, 1);
v___x_1255_ = l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3(v_val_1254_);
v___x_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1256_, 0, v_k_1251_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = lean_box(0);
v___x_1258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1256_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
return v___x_1258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonInitializeParams_toJson(lean_object* v_x_1266_){
_start:
{
lean_object* v_processId_x3f_1267_; lean_object* v_clientInfo_x3f_1268_; lean_object* v_rootUri_x3f_1269_; lean_object* v_initializationOptions_x3f_1270_; lean_object* v_capabilities_1271_; uint8_t v_trace_1272_; lean_object* v_workspaceFolders_x3f_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___y_1289_; 
v_processId_x3f_1267_ = lean_ctor_get(v_x_1266_, 0);
lean_inc(v_processId_x3f_1267_);
v_clientInfo_x3f_1268_ = lean_ctor_get(v_x_1266_, 1);
lean_inc(v_clientInfo_x3f_1268_);
v_rootUri_x3f_1269_ = lean_ctor_get(v_x_1266_, 2);
lean_inc(v_rootUri_x3f_1269_);
v_initializationOptions_x3f_1270_ = lean_ctor_get(v_x_1266_, 3);
lean_inc(v_initializationOptions_x3f_1270_);
v_capabilities_1271_ = lean_ctor_get(v_x_1266_, 4);
lean_inc_ref(v_capabilities_1271_);
v_trace_1272_ = lean_ctor_get_uint8(v_x_1266_, sizeof(void*)*6);
v_workspaceFolders_x3f_1273_ = lean_ctor_get(v_x_1266_, 5);
lean_inc(v_workspaceFolders_x3f_1273_);
lean_dec_ref(v_x_1266_);
v___x_1274_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__0));
v___x_1275_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__0(v___x_1274_, v_processId_x3f_1267_);
v___x_1276_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__1));
v___x_1277_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__1(v___x_1276_, v_clientInfo_x3f_1268_);
v___x_1278_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__2));
v___x_1279_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__0(v___x_1278_, v_rootUri_x3f_1269_);
v___x_1280_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__3));
v___x_1281_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__2(v___x_1280_, v_initializationOptions_x3f_1270_);
v___x_1282_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4));
v___x_1283_ = l_Lean_Lsp_instToJsonClientCapabilities_toJson(v_capabilities_1271_);
v___x_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = lean_box(0);
v___x_1286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1284_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__5));
switch(v_trace_1272_)
{
case 0:
{
lean_object* v___x_1304_; 
v___x_1304_ = ((lean_object*)(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__0));
v___y_1289_ = v___x_1304_;
goto v___jp_1288_;
}
case 1:
{
lean_object* v___x_1305_; 
v___x_1305_ = ((lean_object*)(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__1));
v___y_1289_ = v___x_1305_;
goto v___jp_1288_;
}
default: 
{
lean_object* v___x_1306_; 
v___x_1306_ = ((lean_object*)(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__2));
v___y_1289_ = v___x_1306_;
goto v___jp_1288_;
}
}
v___jp_1288_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
lean_inc(v___y_1289_);
v___x_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1287_);
lean_ctor_set(v___x_1290_, 1, v___y_1289_);
v___x_1291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v___x_1285_);
v___x_1292_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__6));
v___x_1293_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3(v___x_1292_, v_workspaceFolders_x3f_1273_);
v___x_1294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
lean_ctor_set(v___x_1294_, 1, v___x_1285_);
v___x_1295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1291_);
lean_ctor_set(v___x_1295_, 1, v___x_1294_);
v___x_1296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1286_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_1297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1281_);
lean_ctor_set(v___x_1297_, 1, v___x_1296_);
v___x_1298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1279_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
v___x_1299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1277_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
v___x_1300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1275_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
v___x_1301_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2));
v___x_1302_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_1300_, v___x_1301_);
v___x_1303_ = l_Lean_Json_mkObj(v___x_1302_);
lean_dec(v___x_1302_);
return v___x_1303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializeParams___lam__0(lean_object* v___x_1309_, lean_object* v___x_1310_, lean_object* v___x_1311_, lean_object* v___x_1312_, lean_object* v___x_1313_, lean_object* v___x_1314_, lean_object* v___f_1315_, lean_object* v_j_1316_){
_start:
{
lean_object* v___x_1317_; lean_object* v_processId_x3f_1318_; lean_object* v___x_1319_; lean_object* v_clientInfo_x3f_1320_; lean_object* v___x_1321_; lean_object* v_rootUri_x3f_1322_; lean_object* v___x_1323_; lean_object* v_initializationOptions_x3f_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1317_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__0));
lean_inc_n(v_j_1316_, 5);
v_processId_x3f_1318_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1316_, v___x_1309_, v___x_1317_);
v___x_1319_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__1));
v_clientInfo_x3f_1320_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1316_, v___x_1310_, v___x_1319_);
v___x_1321_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__2));
v_rootUri_x3f_1322_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1316_, v___x_1311_, v___x_1321_);
v___x_1323_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__3));
v_initializationOptions_x3f_1324_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1316_, v___x_1312_, v___x_1323_);
v___x_1325_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4));
v___x_1326_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1316_, v___x_1313_, v___x_1325_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec_ref(v_initializationOptions_x3f_1324_);
lean_dec_ref(v_rootUri_x3f_1322_);
lean_dec_ref(v_clientInfo_x3f_1320_);
lean_dec_ref(v_processId_x3f_1318_);
lean_dec(v_j_1316_);
lean_dec_ref(v___f_1315_);
lean_dec_ref(v___x_1314_);
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1426_; 
v_a_1335_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1337_ = v___x_1326_;
v_isShared_1338_ = v_isSharedCheck_1426_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1326_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1426_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___y_1340_; lean_object* v___y_1341_; uint8_t v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1351_; lean_object* v___y_1352_; uint8_t v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1367_; uint8_t v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; uint8_t v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; uint8_t v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; uint8_t v___y_1409_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__5));
lean_inc(v_j_1316_);
v___x_1422_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1316_, v___f_1315_, v___x_1421_);
if (lean_obj_tag(v___x_1422_) == 0)
{
uint8_t v___x_1423_; 
lean_dec_ref_known(v___x_1422_, 1);
v___x_1423_ = 0;
v___y_1409_ = v___x_1423_;
goto v___jp_1408_;
}
else
{
lean_object* v_a_1424_; uint8_t v___x_1425_; 
v_a_1424_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1422_, 1);
v___x_1425_ = lean_unbox(v_a_1424_);
lean_dec(v_a_1424_);
v___y_1409_ = v___x_1425_;
goto v___jp_1408_;
}
v___jp_1339_:
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1346_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1346_, 0, v___y_1343_);
lean_ctor_set(v___x_1346_, 1, v___y_1341_);
lean_ctor_set(v___x_1346_, 2, v___y_1340_);
lean_ctor_set(v___x_1346_, 3, v___y_1344_);
lean_ctor_set(v___x_1346_, 4, v_a_1335_);
lean_ctor_set(v___x_1346_, 5, v___y_1345_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*6, v___y_1342_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1346_);
v___x_1348_ = v___x_1337_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
v___jp_1350_:
{
if (lean_obj_tag(v___y_1354_) == 0)
{
lean_object* v___x_1357_; 
lean_dec_ref_known(v___y_1354_, 1);
v___x_1357_ = lean_box(0);
v___y_1340_ = v___y_1351_;
v___y_1341_ = v___y_1352_;
v___y_1342_ = v___y_1353_;
v___y_1343_ = v___y_1355_;
v___y_1344_ = v___y_1356_;
v___y_1345_ = v___x_1357_;
goto v___jp_1339_;
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
v_a_1358_ = lean_ctor_get(v___y_1354_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___y_1354_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___y_1354_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___y_1354_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
v___y_1340_ = v___y_1351_;
v___y_1341_ = v___y_1352_;
v___y_1342_ = v___y_1353_;
v___y_1343_ = v___y_1355_;
v___y_1344_ = v___y_1356_;
v___y_1345_ = v___x_1363_;
goto v___jp_1339_;
}
}
}
}
v___jp_1366_:
{
if (lean_obj_tag(v_initializationOptions_x3f_1324_) == 0)
{
lean_object* v___x_1372_; 
lean_dec_ref_known(v_initializationOptions_x3f_1324_, 1);
v___x_1372_ = lean_box(0);
v___y_1351_ = v___y_1371_;
v___y_1352_ = v___y_1367_;
v___y_1353_ = v___y_1368_;
v___y_1354_ = v___y_1369_;
v___y_1355_ = v___y_1370_;
v___y_1356_ = v___x_1372_;
goto v___jp_1350_;
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
v_a_1373_ = lean_ctor_get(v_initializationOptions_x3f_1324_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_initializationOptions_x3f_1324_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v_initializationOptions_x3f_1324_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v_initializationOptions_x3f_1324_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
v___y_1351_ = v___y_1371_;
v___y_1352_ = v___y_1367_;
v___y_1353_ = v___y_1368_;
v___y_1354_ = v___y_1369_;
v___y_1355_ = v___y_1370_;
v___y_1356_ = v___x_1378_;
goto v___jp_1350_;
}
}
}
}
v___jp_1381_:
{
if (lean_obj_tag(v_rootUri_x3f_1322_) == 0)
{
lean_object* v___x_1386_; 
lean_dec_ref_known(v_rootUri_x3f_1322_, 1);
v___x_1386_ = lean_box(0);
v___y_1367_ = v___y_1385_;
v___y_1368_ = v___y_1382_;
v___y_1369_ = v___y_1383_;
v___y_1370_ = v___y_1384_;
v___y_1371_ = v___x_1386_;
goto v___jp_1366_;
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
v_a_1387_ = lean_ctor_get(v_rootUri_x3f_1322_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_rootUri_x3f_1322_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v_rootUri_x3f_1322_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v_rootUri_x3f_1322_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
v___y_1367_ = v___y_1385_;
v___y_1368_ = v___y_1382_;
v___y_1369_ = v___y_1383_;
v___y_1370_ = v___y_1384_;
v___y_1371_ = v___x_1392_;
goto v___jp_1366_;
}
}
}
}
v___jp_1395_:
{
if (lean_obj_tag(v_clientInfo_x3f_1320_) == 0)
{
lean_object* v___x_1399_; 
lean_dec_ref_known(v_clientInfo_x3f_1320_, 1);
v___x_1399_ = lean_box(0);
v___y_1382_ = v___y_1396_;
v___y_1383_ = v___y_1397_;
v___y_1384_ = v___y_1398_;
v___y_1385_ = v___x_1399_;
goto v___jp_1381_;
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
v_a_1400_ = lean_ctor_get(v_clientInfo_x3f_1320_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_clientInfo_x3f_1320_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v_clientInfo_x3f_1320_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v_clientInfo_x3f_1320_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
v___y_1382_ = v___y_1396_;
v___y_1383_ = v___y_1397_;
v___y_1384_ = v___y_1398_;
v___y_1385_ = v___x_1405_;
goto v___jp_1381_;
}
}
}
}
v___jp_1408_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__6));
v___x_1411_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1316_, v___x_1314_, v___x_1410_);
if (lean_obj_tag(v_processId_x3f_1318_) == 0)
{
lean_object* v___x_1412_; 
lean_dec_ref_known(v_processId_x3f_1318_, 1);
v___x_1412_ = lean_box(0);
v___y_1396_ = v___y_1409_;
v___y_1397_ = v___x_1411_;
v___y_1398_ = v___x_1412_;
goto v___jp_1395_;
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
v_a_1413_ = lean_ctor_get(v_processId_x3f_1318_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_processId_x3f_1318_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v_processId_x3f_1318_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v_processId_x3f_1318_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
v___y_1396_ = v___y_1409_;
v___y_1397_ = v___x_1411_;
v___y_1398_ = v___x_1418_;
goto v___jp_1395_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializedParams___lam__0(lean_object* v_x_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializedParams___lam__0___closed__0));
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializedParams___lam__0___boxed(lean_object* v_x_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_Lsp_instFromJsonInitializedParams___lam__0(v_x_1446_);
lean_dec(v_x_1446_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonInitializedParams___lam__0(lean_object* v_x_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_box(0);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonServerInfo_toJson(lean_object* v_x_1454_){
_start:
{
lean_object* v_name_1455_; lean_object* v_version_x3f_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1474_; 
v_name_1455_ = lean_ctor_get(v_x_1454_, 0);
v_version_x3f_1456_ = lean_ctor_get(v_x_1454_, 1);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_x_1454_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1458_ = v_x_1454_;
v_isShared_1459_ = v_isSharedCheck_1474_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_version_x3f_1456_);
lean_inc(v_name_1455_);
lean_dec(v_x_1454_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1474_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1463_; 
v___x_1460_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0));
v___x_1461_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1461_, 0, v_name_1455_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 1, v___x_1461_);
lean_ctor_set(v___x_1458_, 0, v___x_1460_);
v___x_1463_ = v___x_1458_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v___x_1461_);
v___x_1463_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1464_ = lean_box(0);
v___x_1465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1463_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v___x_1466_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1));
v___x_1467_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__0(v___x_1466_, v_version_x3f_1456_);
v___x_1468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
lean_ctor_set(v___x_1468_, 1, v___x_1464_);
v___x_1469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1465_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
v___x_1470_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2));
v___x_1471_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_1469_, v___x_1470_);
v___x_1472_ = l_Lean_Json_mkObj(v___x_1471_);
lean_dec(v___x_1471_);
return v___x_1472_;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = 1;
v___x_1483_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1));
v___x_1484_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1483_, v___x_1482_);
return v___x_1484_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1485_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5));
v___x_1486_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2);
v___x_1487_ = lean_string_append(v___x_1486_, v___x_1485_);
return v___x_1487_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1488_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8, &l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8);
v___x_1489_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3);
v___x_1490_ = lean_string_append(v___x_1489_, v___x_1488_);
return v___x_1490_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1491_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_1492_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4);
v___x_1493_ = lean_string_append(v___x_1492_, v___x_1491_);
return v___x_1493_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1494_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14, &l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14);
v___x_1495_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3);
v___x_1496_ = lean_string_append(v___x_1495_, v___x_1494_);
return v___x_1496_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1497_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_1498_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6);
v___x_1499_ = lean_string_append(v___x_1498_, v___x_1497_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonServerInfo_fromJson(lean_object* v_json_1500_){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0));
lean_inc(v_json_1500_);
v___x_1502_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__0(v_json_1500_, v___x_1501_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1512_; 
lean_dec(v_json_1500_);
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1505_ = v___x_1502_;
v_isShared_1506_ = v_isSharedCheck_1512_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1512_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1507_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5);
v___x_1508_ = lean_string_append(v___x_1507_, v_a_1503_);
lean_dec(v_a_1503_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1508_);
v___x_1510_ = v___x_1505_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1508_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
else
{
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec(v_json_1500_);
v_a_1513_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1502_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1502_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set_tag(v___x_1515_, 0);
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v_a_1521_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1521_);
lean_dec_ref_known(v___x_1502_, 1);
v___x_1522_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1));
v___x_1523_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1(v_json_1500_, v___x_1522_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1533_; 
lean_dec(v_a_1521_);
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1526_ = v___x_1523_;
v_isShared_1527_ = v_isSharedCheck_1533_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1523_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1533_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1531_; 
v___x_1528_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7);
v___x_1529_ = lean_string_append(v___x_1528_, v_a_1524_);
lean_dec(v_a_1524_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v___x_1529_);
v___x_1531_ = v___x_1526_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
else
{
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
lean_dec(v_a_1521_);
v_a_1534_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1523_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1523_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
lean_ctor_set_tag(v___x_1536_, 0);
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1550_; 
v_a_1542_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1544_ = v___x_1523_;
v_isShared_1545_ = v_isSharedCheck_1550_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1523_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1550_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1546_; lean_object* v___x_1548_; 
v___x_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1546_, 0, v_a_1521_);
lean_ctor_set(v___x_1546_, 1, v_a_1542_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v___x_1546_);
v___x_1548_ = v___x_1544_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeResult_toJson_spec__0(lean_object* v_k_1553_, lean_object* v_x_1554_){
_start:
{
if (lean_obj_tag(v_x_1554_) == 0)
{
lean_object* v___x_1555_; 
lean_dec_ref(v_k_1553_);
v___x_1555_ = lean_box(0);
return v___x_1555_;
}
else
{
lean_object* v_val_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v_val_1556_ = lean_ctor_get(v_x_1554_, 0);
lean_inc(v_val_1556_);
lean_dec_ref_known(v_x_1554_, 1);
v___x_1557_ = l_Lean_Lsp_instToJsonServerInfo_toJson(v_val_1556_);
v___x_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1558_, 0, v_k_1553_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = lean_box(0);
v___x_1560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1558_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
return v___x_1560_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonInitializeResult_toJson(lean_object* v_x_1562_){
_start:
{
lean_object* v_capabilities_1563_; lean_object* v_serverInfo_x3f_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1582_; 
v_capabilities_1563_ = lean_ctor_get(v_x_1562_, 0);
v_serverInfo_x3f_1564_ = lean_ctor_get(v_x_1562_, 1);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_x_1562_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1566_ = v_x_1562_;
v_isShared_1567_ = v_isSharedCheck_1582_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_serverInfo_x3f_1564_);
lean_inc(v_capabilities_1563_);
lean_dec(v_x_1562_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1582_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
v___x_1568_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4));
v___x_1569_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson(v_capabilities_1563_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 1, v___x_1569_);
lean_ctor_set(v___x_1566_, 0, v___x_1568_);
v___x_1571_ = v___x_1566_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1572_ = lean_box(0);
v___x_1573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1571_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeResult_toJson___closed__0));
v___x_1575_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeResult_toJson_spec__0(v___x_1574_, v_serverInfo_x3f_1564_);
v___x_1576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
lean_ctor_set(v___x_1576_, 1, v___x_1572_);
v___x_1577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1573_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2));
v___x_1579_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_1577_, v___x_1578_);
v___x_1580_ = l_Lean_Json_mkObj(v___x_1579_);
lean_dec(v___x_1579_);
return v___x_1580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0(lean_object* v_j_1585_, lean_object* v_k_1586_){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = l_Lean_Json_getObjValD(v_j_1585_, v_k_1586_);
v___x_1588_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson(v___x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0___boxed(lean_object* v_j_1589_, lean_object* v_k_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0(v_j_1589_, v_k_1590_);
lean_dec_ref(v_k_1590_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1(lean_object* v_x_1594_){
_start:
{
if (lean_obj_tag(v_x_1594_) == 0)
{
lean_object* v___x_1595_; 
v___x_1595_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1___closed__0));
return v___x_1595_;
}
else
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Lean_Lsp_instFromJsonServerInfo_fromJson(v_x_1594_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1596_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1596_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1613_; 
v_a_1605_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1607_ = v___x_1596_;
v_isShared_1608_ = v_isSharedCheck_1613_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1596_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1613_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1609_; lean_object* v___x_1611_; 
v___x_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1609_, 0, v_a_1605_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 0, v___x_1609_);
v___x_1611_ = v___x_1607_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1(lean_object* v_j_1614_, lean_object* v_k_1615_){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = l_Lean_Json_getObjValD(v_j_1614_, v_k_1615_);
v___x_1617_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1(v___x_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1___boxed(lean_object* v_j_1618_, lean_object* v_k_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1(v_j_1618_, v_k_1619_);
lean_dec_ref(v_k_1619_);
return v_res_1620_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1626_ = 1;
v___x_1627_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1));
v___x_1628_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1627_, v___x_1626_);
return v___x_1628_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1629_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5));
v___x_1630_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2);
v___x_1631_ = lean_string_append(v___x_1630_, v___x_1629_);
return v___x_1631_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1634_ = 1;
v___x_1635_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__4));
v___x_1636_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1635_, v___x_1634_);
return v___x_1636_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1637_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5);
v___x_1638_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3);
v___x_1639_ = lean_string_append(v___x_1638_, v___x_1637_);
return v___x_1639_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1640_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_1641_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6);
v___x_1642_ = lean_string_append(v___x_1641_, v___x_1640_);
return v___x_1642_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10(void){
_start:
{
uint8_t v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1646_ = 1;
v___x_1647_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__9));
v___x_1648_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1647_, v___x_1646_);
return v___x_1648_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1649_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10);
v___x_1650_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3);
v___x_1651_ = lean_string_append(v___x_1650_, v___x_1649_);
return v___x_1651_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1652_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_1653_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11);
v___x_1654_ = lean_string_append(v___x_1653_, v___x_1652_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializeResult_fromJson(lean_object* v_json_1655_){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4));
lean_inc(v_json_1655_);
v___x_1657_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0(v_json_1655_, v___x_1656_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1667_; 
lean_dec(v_json_1655_);
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1667_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1667_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1662_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7);
v___x_1663_ = lean_string_append(v___x_1662_, v_a_1658_);
lean_dec(v_a_1658_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1663_);
v___x_1665_ = v___x_1660_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
else
{
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_dec(v_json_1655_);
v_a_1668_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1657_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1657_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set_tag(v___x_1670_, 0);
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v_a_1676_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1676_);
lean_dec_ref_known(v___x_1657_, 1);
v___x_1677_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeResult_toJson___closed__0));
v___x_1678_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1(v_json_1655_, v___x_1677_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1688_; 
lean_dec(v_a_1676_);
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1688_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1688_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1683_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12);
v___x_1684_ = lean_string_append(v___x_1683_, v_a_1679_);
lean_dec(v_a_1679_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v___x_1684_);
v___x_1686_ = v___x_1681_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
else
{
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_dec(v_a_1676_);
v_a_1689_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1678_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1678_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
lean_ctor_set_tag(v___x_1691_, 0);
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1705_; 
v_a_1697_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1699_ = v___x_1678_;
v_isShared_1700_ = v_isSharedCheck_1705_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1678_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1705_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1701_; lean_object* v___x_1703_; 
v___x_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1701_, 0, v_a_1676_);
lean_ctor_set(v___x_1701_, 1, v_a_1697_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 0, v___x_1701_);
v___x_1703_ = v___x_1699_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
}
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_Capabilities(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_Workspace(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_InitShutdown(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Lsp_Capabilities(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Lsp_InitShutdown(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Lsp_Capabilities(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_Workspace(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_InitShutdown(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp_Capabilities(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_InitShutdown(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Lsp_InitShutdown(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Lsp_InitShutdown(builtin);
}
#ifdef __cplusplus
}
#endif
