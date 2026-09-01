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
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Except_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Except_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_pure(lean_object*, lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson(lean_object*);
lean_object* l_Lean_Array_fromJson_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson(lean_object*);
lean_object* l_Lean_Json_getInt_x3f(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__1_value;
static const lean_closure_object l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__2_value;
static const lean_closure_object l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__3_value;
static const lean_closure_object l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__4_value;
static const lean_closure_object l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__5_value;
static const lean_closure_object l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__6_value;
static const lean_ctor_object l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__0_value),((lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__1_value)}};
static const lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__7 = (const lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__7_value;
static const lean_ctor_object l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__7_value),((lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__2_value),((lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__3_value),((lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__4_value),((lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__5_value)}};
static const lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__8 = (const lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__8_value;
static const lean_ctor_object l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__8_value),((lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__6_value)}};
static const lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__9 = (const lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__3(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonHashSet___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonHashSet___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__9_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3;
static const lean_string_object l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "Expected array when converting JSON to Std.HashSet"};
static const lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__4_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__5_value;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__4_value)}};
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLogConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLogConfig_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLogConfig___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLogConfig___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLogConfig = (const lean_object*)&l_Lean_Lsp_instFromJsonLogConfig___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__2(lean_object* v___x_290_, lean_object* v___f_291_, lean_object* v_acc_292_, lean_object* v_l_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_290_, v___f_291_, v_acc_292_, v_l_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__3(lean_object* v___f_314_, lean_object* v___f_315_, lean_object* v_s_316_){
_start:
{
lean_object* v___y_318_; lean_object* v_size_324_; lean_object* v_buckets_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v_size_324_ = lean_ctor_get(v_s_316_, 0);
lean_inc(v_size_324_);
v_buckets_325_ = lean_ctor_get(v_s_316_, 1);
lean_inc_ref(v_buckets_325_);
lean_dec_ref(v_s_316_);
v___x_326_ = lean_mk_empty_array_with_capacity(v_size_324_);
lean_dec(v_size_324_);
v___x_327_ = ((lean_object*)(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__9));
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = lean_array_get_size(v_buckets_325_);
v___x_330_ = lean_nat_dec_lt(v___x_328_, v___x_329_);
if (v___x_330_ == 0)
{
lean_dec_ref(v_buckets_325_);
lean_dec_ref(v___f_315_);
v___y_318_ = v___x_326_;
goto v___jp_317_;
}
else
{
lean_object* v___f_331_; size_t v___x_332_; size_t v___x_333_; lean_object* v___x_334_; 
v___f_331_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonHashSet___redArg___lam__2), 4, 2);
lean_closure_set(v___f_331_, 0, v___x_327_);
lean_closure_set(v___f_331_, 1, v___f_315_);
v___x_332_ = ((size_t)0ULL);
v___x_333_ = lean_usize_of_nat(v___x_329_);
v___x_334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_327_, v___f_331_, v_buckets_325_, v___x_332_, v___x_333_, v___x_326_);
v___y_318_ = v___x_334_;
goto v___jp_317_;
}
v___jp_317_:
{
lean_object* v___x_319_; size_t v_sz_320_; size_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_319_ = ((lean_object*)(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__9));
v_sz_320_ = lean_array_size(v___y_318_);
v___x_321_ = ((size_t)0ULL);
v___x_322_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_319_, v___f_314_, v_sz_320_, v___x_321_, v___y_318_);
v___x_323_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg(lean_object* v_inst_336_){
_start:
{
lean_object* v___f_337_; lean_object* v___f_338_; lean_object* v___f_339_; 
v___f_337_ = ((lean_object*)(l_Lean_Lsp_instToJsonHashSet___redArg___closed__0));
v___f_338_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_338_, 0, v_inst_336_);
v___f_339_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3), 3, 2);
lean_closure_set(v___f_339_, 0, v___f_338_);
lean_closure_set(v___f_339_, 1, v___f_337_);
return v___f_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet(lean_object* v_00_u03b1_340_, lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_inst_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_Lsp_instToJsonHashSet___redArg(v_inst_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___boxed(lean_object* v_00_u03b1_345_, lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_inst_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Lsp_instToJsonHashSet(v_00_u03b1_345_, v_inst_346_, v_inst_347_, v_inst_348_);
lean_dec_ref(v_inst_347_);
lean_dec_ref(v_inst_346_);
return v_res_349_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_354_ = lean_box(0);
v___x_355_ = lean_unsigned_to_nat(16u);
v___x_356_ = lean_mk_array(v___x_355_, v___x_354_);
return v___x_356_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = lean_obj_once(&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2, &l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2_once, _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2);
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v___x_357_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0(lean_object* v___x_363_, lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_x_367_){
_start:
{
if (lean_obj_tag(v_x_367_) == 4)
{
lean_object* v_elems_368_; size_t v_sz_369_; size_t v___x_370_; lean_object* v___x_371_; 
v_elems_368_ = lean_ctor_get(v_x_367_, 0);
lean_inc_ref(v_elems_368_);
lean_dec_ref_known(v_x_367_, 1);
v_sz_369_ = lean_array_size(v_elems_368_);
v___x_370_ = ((size_t)0ULL);
v___x_371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_363_, v_inst_364_, v_sz_369_, v___x_370_, v_elems_368_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_dec_ref(v_inst_366_);
lean_dec_ref(v_inst_365_);
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_390_; 
v_a_380_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_390_ == 0)
{
v___x_382_ = v___x_371_;
v_isShared_383_ = v_isSharedCheck_390_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_371_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_390_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___f_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v___f_384_ = ((lean_object*)(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__1));
v___x_385_ = lean_obj_once(&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3, &l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3_once, _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3);
v___x_386_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_384_, v_inst_365_, v_inst_366_, v___x_385_, v_a_380_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_386_);
v___x_388_ = v___x_382_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
else
{
lean_object* v___x_391_; 
lean_dec(v_x_367_);
lean_dec_ref(v_inst_366_);
lean_dec_ref(v_inst_365_);
lean_dec_ref(v_inst_364_);
lean_dec_ref(v___x_363_);
v___x_391_ = ((lean_object*)(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__5));
return v___x_391_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg(lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_inst_413_){
_start:
{
lean_object* v___x_414_; lean_object* v___f_415_; 
v___x_414_ = ((lean_object*)(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__9));
v___f_415_ = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0), 5, 4);
lean_closure_set(v___f_415_, 0, v___x_414_);
lean_closure_set(v___f_415_, 1, v_inst_413_);
lean_closure_set(v___f_415_, 2, v_inst_411_);
lean_closure_set(v___f_415_, 3, v_inst_412_);
return v___f_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHashSet(lean_object* v_00_u03b1_416_, lean_object* v_inst_417_, lean_object* v_inst_418_, lean_object* v_inst_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_Lsp_instFromJsonHashSet___redArg(v_inst_417_, v_inst_418_, v_inst_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0_spec__0(lean_object* v_x_421_){
_start:
{
if (lean_obj_tag(v_x_421_) == 0)
{
lean_object* v___x_422_; 
v___x_422_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1___closed__0));
return v___x_422_;
}
else
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_Json_getStr_x3f(v_x_421_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_423_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_423_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_440_; 
v_a_432_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_440_ == 0)
{
v___x_434_ = v___x_423_;
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_423_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_436_, 0, v_a_432_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_436_);
v___x_438_ = v___x_434_;
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
return v___x_438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0(lean_object* v_j_441_, lean_object* v_k_442_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = l_Lean_Json_getObjValD(v_j_441_, v_k_442_);
v___x_444_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0_spec__0(v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0___boxed(lean_object* v_j_445_, lean_object* v_k_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0(v_j_445_, v_k_446_);
lean_dec_ref(v_k_446_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10___redArg(lean_object* v_x_448_, lean_object* v_x_449_){
_start:
{
if (lean_obj_tag(v_x_449_) == 0)
{
return v_x_448_;
}
else
{
lean_object* v_key_450_; lean_object* v_value_451_; lean_object* v_tail_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_475_; 
v_key_450_ = lean_ctor_get(v_x_449_, 0);
v_value_451_ = lean_ctor_get(v_x_449_, 1);
v_tail_452_ = lean_ctor_get(v_x_449_, 2);
v_isSharedCheck_475_ = !lean_is_exclusive(v_x_449_);
if (v_isSharedCheck_475_ == 0)
{
v___x_454_ = v_x_449_;
v_isShared_455_ = v_isSharedCheck_475_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_tail_452_);
lean_inc(v_value_451_);
lean_inc(v_key_450_);
lean_dec(v_x_449_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_475_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; uint64_t v___x_457_; uint64_t v___x_458_; uint64_t v___x_459_; uint64_t v_fold_460_; uint64_t v___x_461_; uint64_t v___x_462_; uint64_t v___x_463_; size_t v___x_464_; size_t v___x_465_; size_t v___x_466_; size_t v___x_467_; size_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_456_ = lean_array_get_size(v_x_448_);
v___x_457_ = lean_string_hash(v_key_450_);
v___x_458_ = 32ULL;
v___x_459_ = lean_uint64_shift_right(v___x_457_, v___x_458_);
v_fold_460_ = lean_uint64_xor(v___x_457_, v___x_459_);
v___x_461_ = 16ULL;
v___x_462_ = lean_uint64_shift_right(v_fold_460_, v___x_461_);
v___x_463_ = lean_uint64_xor(v_fold_460_, v___x_462_);
v___x_464_ = lean_uint64_to_usize(v___x_463_);
v___x_465_ = lean_usize_of_nat(v___x_456_);
v___x_466_ = ((size_t)1ULL);
v___x_467_ = lean_usize_sub(v___x_465_, v___x_466_);
v___x_468_ = lean_usize_land(v___x_464_, v___x_467_);
v___x_469_ = lean_array_uget_borrowed(v_x_448_, v___x_468_);
lean_inc(v___x_469_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 2, v___x_469_);
v___x_471_ = v___x_454_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_key_450_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_value_451_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v___x_469_);
v___x_471_ = v_reuseFailAlloc_474_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; 
v___x_472_ = lean_array_uset(v_x_448_, v___x_468_, v___x_471_);
v_x_448_ = v___x_472_;
v_x_449_ = v_tail_452_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8___redArg(lean_object* v_i_476_, lean_object* v_source_477_, lean_object* v_target_478_){
_start:
{
lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = lean_array_get_size(v_source_477_);
v___x_480_ = lean_nat_dec_lt(v_i_476_, v___x_479_);
if (v___x_480_ == 0)
{
lean_dec_ref(v_source_477_);
lean_dec(v_i_476_);
return v_target_478_;
}
else
{
lean_object* v_es_481_; lean_object* v___x_482_; lean_object* v_source_483_; lean_object* v_target_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_es_481_ = lean_array_fget(v_source_477_, v_i_476_);
v___x_482_ = lean_box(0);
v_source_483_ = lean_array_fset(v_source_477_, v_i_476_, v___x_482_);
v_target_484_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10___redArg(v_target_478_, v_es_481_);
v___x_485_ = lean_unsigned_to_nat(1u);
v___x_486_ = lean_nat_add(v_i_476_, v___x_485_);
lean_dec(v_i_476_);
v_i_476_ = v___x_486_;
v_source_477_ = v_source_483_;
v_target_478_ = v_target_484_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_data_488_){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v_nbuckets_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_489_ = lean_array_get_size(v_data_488_);
v___x_490_ = lean_unsigned_to_nat(2u);
v_nbuckets_491_ = lean_nat_mul(v___x_489_, v___x_490_);
v___x_492_ = lean_unsigned_to_nat(0u);
v___x_493_ = lean_box(0);
v___x_494_ = lean_mk_array(v_nbuckets_491_, v___x_493_);
v___x_495_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8___redArg(v___x_492_, v_data_488_, v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_a_496_, lean_object* v_x_497_){
_start:
{
if (lean_obj_tag(v_x_497_) == 0)
{
uint8_t v___x_498_; 
v___x_498_ = 0;
return v___x_498_;
}
else
{
lean_object* v_key_499_; lean_object* v_tail_500_; uint8_t v___x_501_; 
v_key_499_ = lean_ctor_get(v_x_497_, 0);
v_tail_500_ = lean_ctor_get(v_x_497_, 2);
v___x_501_ = lean_string_dec_eq(v_key_499_, v_a_496_);
if (v___x_501_ == 0)
{
v_x_497_ = v_tail_500_;
goto _start;
}
else
{
return v___x_501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_a_503_, lean_object* v_x_504_){
_start:
{
uint8_t v_res_505_; lean_object* v_r_506_; 
v_res_505_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_a_503_, v_x_504_);
lean_dec(v_x_504_);
lean_dec_ref(v_a_503_);
v_r_506_ = lean_box(v_res_505_);
return v_r_506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_m_507_, lean_object* v_a_508_, lean_object* v_b_509_){
_start:
{
lean_object* v_size_510_; lean_object* v_buckets_511_; lean_object* v___x_512_; uint64_t v___x_513_; uint64_t v___x_514_; uint64_t v___x_515_; uint64_t v_fold_516_; uint64_t v___x_517_; uint64_t v___x_518_; uint64_t v___x_519_; size_t v___x_520_; size_t v___x_521_; size_t v___x_522_; size_t v___x_523_; size_t v___x_524_; lean_object* v_bkt_525_; uint8_t v___x_526_; 
v_size_510_ = lean_ctor_get(v_m_507_, 0);
v_buckets_511_ = lean_ctor_get(v_m_507_, 1);
v___x_512_ = lean_array_get_size(v_buckets_511_);
v___x_513_ = lean_string_hash(v_a_508_);
v___x_514_ = 32ULL;
v___x_515_ = lean_uint64_shift_right(v___x_513_, v___x_514_);
v_fold_516_ = lean_uint64_xor(v___x_513_, v___x_515_);
v___x_517_ = 16ULL;
v___x_518_ = lean_uint64_shift_right(v_fold_516_, v___x_517_);
v___x_519_ = lean_uint64_xor(v_fold_516_, v___x_518_);
v___x_520_ = lean_uint64_to_usize(v___x_519_);
v___x_521_ = lean_usize_of_nat(v___x_512_);
v___x_522_ = ((size_t)1ULL);
v___x_523_ = lean_usize_sub(v___x_521_, v___x_522_);
v___x_524_ = lean_usize_land(v___x_520_, v___x_523_);
v_bkt_525_ = lean_array_uget_borrowed(v_buckets_511_, v___x_524_);
v___x_526_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_a_508_, v_bkt_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_547_; 
lean_inc_ref(v_buckets_511_);
lean_inc(v_size_510_);
v_isSharedCheck_547_ = !lean_is_exclusive(v_m_507_);
if (v_isSharedCheck_547_ == 0)
{
lean_object* v_unused_548_; lean_object* v_unused_549_; 
v_unused_548_ = lean_ctor_get(v_m_507_, 1);
lean_dec(v_unused_548_);
v_unused_549_ = lean_ctor_get(v_m_507_, 0);
lean_dec(v_unused_549_);
v___x_528_ = v_m_507_;
v_isShared_529_ = v_isSharedCheck_547_;
goto v_resetjp_527_;
}
else
{
lean_dec(v_m_507_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_547_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v_size_x27_531_; lean_object* v___x_532_; lean_object* v_buckets_x27_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_530_ = lean_unsigned_to_nat(1u);
v_size_x27_531_ = lean_nat_add(v_size_510_, v___x_530_);
lean_dec(v_size_510_);
lean_inc(v_bkt_525_);
v___x_532_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_532_, 0, v_a_508_);
lean_ctor_set(v___x_532_, 1, v_b_509_);
lean_ctor_set(v___x_532_, 2, v_bkt_525_);
v_buckets_x27_533_ = lean_array_uset(v_buckets_511_, v___x_524_, v___x_532_);
v___x_534_ = lean_unsigned_to_nat(4u);
v___x_535_ = lean_nat_mul(v_size_x27_531_, v___x_534_);
v___x_536_ = lean_unsigned_to_nat(3u);
v___x_537_ = lean_nat_div(v___x_535_, v___x_536_);
lean_dec(v___x_535_);
v___x_538_ = lean_array_get_size(v_buckets_x27_533_);
v___x_539_ = lean_nat_dec_le(v___x_537_, v___x_538_);
lean_dec(v___x_537_);
if (v___x_539_ == 0)
{
lean_object* v_val_540_; lean_object* v___x_542_; 
v_val_540_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7___redArg(v_buckets_x27_533_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 1, v_val_540_);
lean_ctor_set(v___x_528_, 0, v_size_x27_531_);
v___x_542_ = v___x_528_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_size_x27_531_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_val_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
else
{
lean_object* v___x_545_; 
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 1, v_buckets_x27_533_);
lean_ctor_set(v___x_528_, 0, v_size_x27_531_);
v___x_545_ = v___x_528_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_size_x27_531_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_buckets_x27_533_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
else
{
lean_dec(v_b_509_);
lean_dec_ref(v_a_508_);
return v_m_507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6(lean_object* v_as_550_, size_t v_sz_551_, size_t v_i_552_, lean_object* v_b_553_){
_start:
{
uint8_t v___x_554_; 
v___x_554_ = lean_usize_dec_lt(v_i_552_, v_sz_551_);
if (v___x_554_ == 0)
{
return v_b_553_;
}
else
{
lean_object* v_a_555_; lean_object* v___x_556_; lean_object* v_r_557_; size_t v___x_558_; size_t v___x_559_; 
v_a_555_ = lean_array_uget_borrowed(v_as_550_, v_i_552_);
v___x_556_ = lean_box(0);
lean_inc(v_a_555_);
v_r_557_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(v_b_553_, v_a_555_, v___x_556_);
v___x_558_ = ((size_t)1ULL);
v___x_559_ = lean_usize_add(v_i_552_, v___x_558_);
v_i_552_ = v___x_559_;
v_b_553_ = v_r_557_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_as_561_, lean_object* v_sz_562_, lean_object* v_i_563_, lean_object* v_b_564_){
_start:
{
size_t v_sz_boxed_565_; size_t v_i_boxed_566_; lean_object* v_res_567_; 
v_sz_boxed_565_ = lean_unbox_usize(v_sz_562_);
lean_dec(v_sz_562_);
v_i_boxed_566_ = lean_unbox_usize(v_i_563_);
lean_dec(v_i_563_);
v_res_567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6(v_as_561_, v_sz_boxed_565_, v_i_boxed_566_, v_b_564_);
lean_dec_ref(v_as_561_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4(lean_object* v_m_568_, lean_object* v_l_569_){
_start:
{
size_t v_sz_570_; size_t v___x_571_; lean_object* v___x_572_; 
v_sz_570_ = lean_array_size(v_l_569_);
v___x_571_ = ((size_t)0ULL);
v___x_572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6(v_l_569_, v_sz_570_, v___x_571_, v_m_568_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4___boxed(lean_object* v_m_573_, lean_object* v_l_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4(v_m_573_, v_l_574_);
lean_dec_ref(v_l_574_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3(size_t v_sz_576_, size_t v_i_577_, lean_object* v_bs_578_){
_start:
{
uint8_t v___x_579_; 
v___x_579_ = lean_usize_dec_lt(v_i_577_, v_sz_576_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; 
v___x_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_580_, 0, v_bs_578_);
return v___x_580_;
}
else
{
lean_object* v_v_581_; lean_object* v___x_582_; 
v_v_581_ = lean_array_uget_borrowed(v_bs_578_, v_i_577_);
lean_inc(v_v_581_);
v___x_582_ = l_Lean_Json_getStr_x3f(v_v_581_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec_ref(v_bs_578_);
v_a_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_592_; lean_object* v_bs_x27_593_; size_t v___x_594_; size_t v___x_595_; lean_object* v___x_596_; 
v_a_591_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_591_);
lean_dec_ref_known(v___x_582_, 1);
v___x_592_ = lean_unsigned_to_nat(0u);
v_bs_x27_593_ = lean_array_uset(v_bs_578_, v_i_577_, v___x_592_);
v___x_594_ = ((size_t)1ULL);
v___x_595_ = lean_usize_add(v_i_577_, v___x_594_);
v___x_596_ = lean_array_uset(v_bs_x27_593_, v_i_577_, v_a_591_);
v_i_577_ = v___x_595_;
v_bs_578_ = v___x_596_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3___boxed(lean_object* v_sz_598_, lean_object* v_i_599_, lean_object* v_bs_600_){
_start:
{
size_t v_sz_boxed_601_; size_t v_i_boxed_602_; lean_object* v_res_603_; 
v_sz_boxed_601_ = lean_unbox_usize(v_sz_598_);
lean_dec(v_sz_598_);
v_i_boxed_602_ = lean_unbox_usize(v_i_599_);
lean_dec(v_i_599_);
v_res_603_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3(v_sz_boxed_601_, v_i_boxed_602_, v_bs_600_);
return v_res_603_;
}
}
static lean_object* _init_l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_606_ = lean_box(0);
v___x_607_ = lean_unsigned_to_nat(16u);
v___x_608_ = lean_mk_array(v___x_607_, v___x_606_);
return v___x_608_;
}
}
static lean_object* _init_l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_609_ = lean_obj_once(&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1, &l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1_once, _init_l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1);
v___x_610_ = lean_unsigned_to_nat(0u);
v___x_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v___x_609_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2(lean_object* v_x_614_){
_start:
{
if (lean_obj_tag(v_x_614_) == 0)
{
lean_object* v___x_615_; 
v___x_615_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__0));
return v___x_615_;
}
else
{
if (lean_obj_tag(v_x_614_) == 4)
{
lean_object* v_elems_616_; size_t v_sz_617_; size_t v___x_618_; lean_object* v___x_619_; 
v_elems_616_ = lean_ctor_get(v_x_614_, 0);
lean_inc_ref(v_elems_616_);
lean_dec_ref_known(v_x_614_, 1);
v_sz_617_ = lean_array_size(v_elems_616_);
v___x_618_ = ((size_t)0ULL);
v___x_619_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3(v_sz_617_, v___x_618_, v_elems_616_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_619_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_619_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_638_; 
v_a_628_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_638_ == 0)
{
v___x_630_ = v___x_619_;
v_isShared_631_ = v_isSharedCheck_638_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_619_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_638_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_632_ = lean_obj_once(&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2, &l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2_once, _init_l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2);
v___x_633_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4(v___x_632_, v_a_628_);
lean_dec(v_a_628_);
v___x_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_634_);
v___x_636_ = v___x_630_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
else
{
lean_object* v___x_639_; 
lean_dec(v_x_614_);
v___x_639_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__3));
return v___x_639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(lean_object* v_j_640_, lean_object* v_k_641_){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = l_Lean_Json_getObjValD(v_j_640_, v_k_641_);
v___x_643_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2(v___x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1___boxed(lean_object* v_j_644_, lean_object* v_k_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(v_j_644_, v_k_645_);
lean_dec_ref(v_k_645_);
return v_res_646_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3(void){
_start:
{
uint8_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_653_ = 1;
v___x_654_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2));
v___x_655_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_654_, v___x_653_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5));
v___x_657_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3);
v___x_658_ = lean_string_append(v___x_657_, v___x_656_);
return v___x_658_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7(void){
_start:
{
uint8_t v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_662_ = 1;
v___x_663_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__6));
v___x_664_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_663_, v___x_662_);
return v___x_664_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7);
v___x_666_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4);
v___x_667_ = lean_string_append(v___x_666_, v___x_665_);
return v___x_667_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_669_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8);
v___x_670_ = lean_string_append(v___x_669_, v___x_668_);
return v___x_670_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13(void){
_start:
{
uint8_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = 1;
v___x_676_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__12));
v___x_677_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_676_, v___x_675_);
return v___x_677_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_678_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13);
v___x_679_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4);
v___x_680_ = lean_string_append(v___x_679_, v___x_678_);
return v___x_680_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_682_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14);
v___x_683_ = lean_string_append(v___x_682_, v___x_681_);
return v___x_683_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19(void){
_start:
{
uint8_t v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_688_ = 1;
v___x_689_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__18));
v___x_690_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_689_, v___x_688_);
return v___x_690_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_691_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19);
v___x_692_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4);
v___x_693_ = lean_string_append(v___x_692_, v___x_691_);
return v___x_693_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_695_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20);
v___x_696_ = lean_string_append(v___x_695_, v___x_694_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson(lean_object* v_json_697_){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__0));
lean_inc(v_json_697_);
v___x_699_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0(v_json_697_, v___x_698_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_709_; 
lean_dec(v_json_697_);
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_709_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_709_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_709_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_707_; 
v___x_704_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9);
v___x_705_ = lean_string_append(v___x_704_, v_a_700_);
lean_dec(v_a_700_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_705_);
v___x_707_ = v___x_702_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
else
{
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec(v_json_697_);
v_a_710_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_699_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_699_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
lean_ctor_set_tag(v___x_712_, 0);
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_a_718_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_699_, 1);
v___x_719_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__10));
lean_inc(v_json_697_);
v___x_720_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(v_json_697_, v___x_719_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_730_; 
lean_dec(v_a_718_);
lean_dec(v_json_697_);
v_a_721_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_730_ == 0)
{
v___x_723_ = v___x_720_;
v_isShared_724_ = v_isSharedCheck_730_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_730_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_725_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15);
v___x_726_ = lean_string_append(v___x_725_, v_a_721_);
lean_dec(v_a_721_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_726_);
v___x_728_ = v___x_723_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec(v_a_718_);
lean_dec(v_json_697_);
v_a_731_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_720_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_720_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 0);
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v_a_739_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_720_, 1);
v___x_740_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__16));
v___x_741_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(v_json_697_, v___x_740_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_751_; 
lean_dec(v_a_739_);
lean_dec(v_a_718_);
v_a_742_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_751_ == 0)
{
v___x_744_ = v___x_741_;
v_isShared_745_ = v_isSharedCheck_751_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_741_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_751_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_746_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21);
v___x_747_ = lean_string_append(v___x_746_, v_a_742_);
lean_dec(v_a_742_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_747_);
v___x_749_ = v___x_744_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
else
{
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec(v_a_739_);
lean_dec(v_a_718_);
v_a_752_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_741_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_741_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
lean_ctor_set_tag(v___x_754_, 0);
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_768_; 
v_a_760_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_768_ == 0)
{
v___x_762_ = v___x_741_;
v_isShared_763_ = v_isSharedCheck_768_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_741_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_768_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_764_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_764_, 0, v_a_718_);
lean_ctor_set(v___x_764_, 1, v_a_739_);
lean_ctor_set(v___x_764_, 2, v_a_760_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v___x_764_);
v___x_766_ = v___x_762_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_769_, lean_object* v_m_770_, lean_object* v_a_771_, lean_object* v_b_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(v_m_770_, v_a_771_, v_b_772_);
return v___x_773_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_774_, lean_object* v_a_775_, lean_object* v_x_776_){
_start:
{
uint8_t v___x_777_; 
v___x_777_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_a_775_, v_x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_00_u03b2_778_, lean_object* v_a_779_, lean_object* v_x_780_){
_start:
{
uint8_t v_res_781_; lean_object* v_r_782_; 
v_res_781_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6(v_00_u03b2_778_, v_a_779_, v_x_780_);
lean_dec(v_x_780_);
lean_dec_ref(v_a_779_);
v_r_782_ = lean_box(v_res_781_);
return v_r_782_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_783_, lean_object* v_data_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7___redArg(v_data_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8(lean_object* v_00_u03b2_786_, lean_object* v_i_787_, lean_object* v_source_788_, lean_object* v_target_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8___redArg(v_i_787_, v_source_788_, v_target_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10(lean_object* v_00_u03b2_791_, lean_object* v_x_792_, lean_object* v_x_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10___redArg(v_x_792_, v_x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__0(lean_object* v_k_797_, lean_object* v_x_798_){
_start:
{
if (lean_obj_tag(v_x_798_) == 0)
{
lean_object* v___x_799_; 
lean_dec_ref(v_k_797_);
v___x_799_ = lean_box(0);
return v___x_799_;
}
else
{
lean_object* v_val_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_810_; 
v_val_800_ = lean_ctor_get(v_x_798_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v_x_798_);
if (v_isSharedCheck_810_ == 0)
{
v___x_802_ = v_x_798_;
v_isShared_803_ = v_isSharedCheck_810_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_val_800_);
lean_dec(v_x_798_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_810_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
lean_ctor_set_tag(v___x_802_, 3);
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_val_800_);
v___x_805_ = v_reuseFailAlloc_809_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v_k_797_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = lean_box(0);
v___x_808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
return v___x_808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1(size_t v_sz_811_, size_t v_i_812_, lean_object* v_bs_813_){
_start:
{
uint8_t v___x_814_; 
v___x_814_ = lean_usize_dec_lt(v_i_812_, v_sz_811_);
if (v___x_814_ == 0)
{
return v_bs_813_;
}
else
{
lean_object* v_v_815_; lean_object* v___x_816_; lean_object* v_bs_x27_817_; lean_object* v___x_818_; size_t v___x_819_; size_t v___x_820_; lean_object* v___x_821_; 
v_v_815_ = lean_array_uget(v_bs_813_, v_i_812_);
v___x_816_ = lean_unsigned_to_nat(0u);
v_bs_x27_817_ = lean_array_uset(v_bs_813_, v_i_812_, v___x_816_);
v___x_818_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_818_, 0, v_v_815_);
v___x_819_ = ((size_t)1ULL);
v___x_820_ = lean_usize_add(v_i_812_, v___x_819_);
v___x_821_ = lean_array_uset(v_bs_x27_817_, v_i_812_, v___x_818_);
v_i_812_ = v___x_820_;
v_bs_813_ = v___x_821_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1___boxed(lean_object* v_sz_823_, lean_object* v_i_824_, lean_object* v_bs_825_){
_start:
{
size_t v_sz_boxed_826_; size_t v_i_boxed_827_; lean_object* v_res_828_; 
v_sz_boxed_826_ = lean_unbox_usize(v_sz_823_);
lean_dec(v_sz_823_);
v_i_boxed_827_ = lean_unbox_usize(v_i_824_);
lean_dec(v_i_824_);
v_res_828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1(v_sz_boxed_826_, v_i_boxed_827_, v_bs_825_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__2(lean_object* v_x_829_, lean_object* v_x_830_){
_start:
{
if (lean_obj_tag(v_x_830_) == 0)
{
return v_x_829_;
}
else
{
lean_object* v_key_831_; lean_object* v_tail_832_; lean_object* v___x_833_; 
v_key_831_ = lean_ctor_get(v_x_830_, 0);
lean_inc(v_key_831_);
v_tail_832_ = lean_ctor_get(v_x_830_, 2);
lean_inc(v_tail_832_);
lean_dec_ref_known(v_x_830_, 3);
v___x_833_ = lean_array_push(v_x_829_, v_key_831_);
v_x_829_ = v___x_833_;
v_x_830_ = v_tail_832_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__3(lean_object* v_as_835_, size_t v_i_836_, size_t v_stop_837_, lean_object* v_b_838_){
_start:
{
uint8_t v___x_839_; 
v___x_839_ = lean_usize_dec_eq(v_i_836_, v_stop_837_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; size_t v___x_842_; size_t v___x_843_; 
v___x_840_ = lean_array_uget_borrowed(v_as_835_, v_i_836_);
lean_inc(v___x_840_);
v___x_841_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__2(v_b_838_, v___x_840_);
v___x_842_ = ((size_t)1ULL);
v___x_843_ = lean_usize_add(v_i_836_, v___x_842_);
v_i_836_ = v___x_843_;
v_b_838_ = v___x_841_;
goto _start;
}
else
{
return v_b_838_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__3___boxed(lean_object* v_as_845_, lean_object* v_i_846_, lean_object* v_stop_847_, lean_object* v_b_848_){
_start:
{
size_t v_i_boxed_849_; size_t v_stop_boxed_850_; lean_object* v_res_851_; 
v_i_boxed_849_ = lean_unbox_usize(v_i_846_);
lean_dec(v_i_846_);
v_stop_boxed_850_ = lean_unbox_usize(v_stop_847_);
lean_dec(v_stop_847_);
v_res_851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__3(v_as_845_, v_i_boxed_849_, v_stop_boxed_850_, v_b_848_);
lean_dec_ref(v_as_845_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(lean_object* v_k_852_, lean_object* v_x_853_){
_start:
{
lean_object* v___y_855_; 
if (lean_obj_tag(v_x_853_) == 0)
{
lean_object* v___x_863_; 
lean_dec_ref(v_k_852_);
v___x_863_ = lean_box(0);
return v___x_863_;
}
else
{
lean_object* v_val_864_; lean_object* v_size_865_; lean_object* v_buckets_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v_val_864_ = lean_ctor_get(v_x_853_, 0);
v_size_865_ = lean_ctor_get(v_val_864_, 0);
v_buckets_866_ = lean_ctor_get(v_val_864_, 1);
v___x_867_ = lean_mk_empty_array_with_capacity(v_size_865_);
v___x_868_ = lean_unsigned_to_nat(0u);
v___x_869_ = lean_array_get_size(v_buckets_866_);
v___x_870_ = lean_nat_dec_lt(v___x_868_, v___x_869_);
if (v___x_870_ == 0)
{
v___y_855_ = v___x_867_;
goto v___jp_854_;
}
else
{
size_t v___x_871_; size_t v___x_872_; lean_object* v___x_873_; 
v___x_871_ = ((size_t)0ULL);
v___x_872_ = lean_usize_of_nat(v___x_869_);
v___x_873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__3(v_buckets_866_, v___x_871_, v___x_872_, v___x_867_);
v___y_855_ = v___x_873_;
goto v___jp_854_;
}
}
v___jp_854_:
{
size_t v_sz_856_; size_t v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v_sz_856_ = lean_array_size(v___y_855_);
v___x_857_ = ((size_t)0ULL);
v___x_858_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1(v_sz_856_, v___x_857_, v___y_855_);
v___x_859_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v_k_852_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = lean_box(0);
v___x_862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1___boxed(lean_object* v_k_874_, lean_object* v_x_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(v_k_874_, v_x_875_);
lean_dec(v_x_875_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLogConfig_toJson(lean_object* v_x_877_){
_start:
{
lean_object* v_logDir_x3f_878_; lean_object* v_allowedMethods_x3f_879_; lean_object* v_disallowedMethods_x3f_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_logDir_x3f_878_ = lean_ctor_get(v_x_877_, 0);
lean_inc(v_logDir_x3f_878_);
v_allowedMethods_x3f_879_ = lean_ctor_get(v_x_877_, 1);
lean_inc(v_allowedMethods_x3f_879_);
v_disallowedMethods_x3f_880_ = lean_ctor_get(v_x_877_, 2);
lean_inc(v_disallowedMethods_x3f_880_);
lean_dec_ref(v_x_877_);
v___x_881_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__0));
v___x_882_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__0(v___x_881_, v_logDir_x3f_878_);
v___x_883_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__10));
v___x_884_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(v___x_883_, v_allowedMethods_x3f_879_);
lean_dec(v_allowedMethods_x3f_879_);
v___x_885_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__16));
v___x_886_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(v___x_885_, v_disallowedMethods_x3f_880_);
lean_dec(v_disallowedMethods_x3f_880_);
v___x_887_ = lean_box(0);
v___x_888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_884_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_882_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2));
v___x_892_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_890_, v___x_891_);
v___x_893_ = l_Lean_Json_mkObj(v___x_892_);
lean_dec(v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0(lean_object* v_k_896_, lean_object* v_x_897_){
_start:
{
if (lean_obj_tag(v_x_897_) == 0)
{
lean_object* v___x_898_; 
lean_dec_ref(v_k_896_);
v___x_898_ = lean_box(0);
return v___x_898_;
}
else
{
lean_object* v_val_899_; lean_object* v___x_900_; uint8_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v_val_899_ = lean_ctor_get(v_x_897_, 0);
v___x_900_ = lean_alloc_ctor(1, 0, 1);
v___x_901_ = lean_unbox(v_val_899_);
lean_ctor_set_uint8(v___x_900_, 0, v___x_901_);
v___x_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_902_, 0, v_k_896_);
lean_ctor_set(v___x_902_, 1, v___x_900_);
v___x_903_ = lean_box(0);
v___x_904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
return v___x_904_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0___boxed(lean_object* v_k_905_, lean_object* v_x_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0(v_k_905_, v_x_906_);
lean_dec(v_x_906_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__1(lean_object* v_k_908_, lean_object* v_x_909_){
_start:
{
if (lean_obj_tag(v_x_909_) == 0)
{
lean_object* v___x_910_; 
lean_dec_ref(v_k_908_);
v___x_910_ = lean_box(0);
return v___x_910_;
}
else
{
lean_object* v_val_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_val_911_ = lean_ctor_get(v_x_909_, 0);
lean_inc(v_val_911_);
lean_dec_ref_known(v_x_909_, 1);
v___x_912_ = l_Lean_Lsp_instToJsonLogConfig_toJson(v_val_911_);
v___x_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_913_, 0, v_k_908_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_box(0);
v___x_915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
return v___x_915_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonInitializationOptions_toJson(lean_object* v_x_918_){
_start:
{
lean_object* v_hasWidgets_x3f_919_; lean_object* v_logCfg_x3f_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_936_; 
v_hasWidgets_x3f_919_ = lean_ctor_get(v_x_918_, 0);
v_logCfg_x3f_920_ = lean_ctor_get(v_x_918_, 1);
v_isSharedCheck_936_ = !lean_is_exclusive(v_x_918_);
if (v_isSharedCheck_936_ == 0)
{
v___x_922_ = v_x_918_;
v_isShared_923_ = v_isSharedCheck_936_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_logCfg_x3f_920_);
lean_inc(v_hasWidgets_x3f_919_);
lean_dec(v_x_918_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_936_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_924_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__0));
v___x_925_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0(v___x_924_, v_hasWidgets_x3f_919_);
lean_dec(v_hasWidgets_x3f_919_);
v___x_926_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__1));
v___x_927_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__1(v___x_926_, v_logCfg_x3f_920_);
v___x_928_ = lean_box(0);
if (v_isShared_923_ == 0)
{
lean_ctor_set_tag(v___x_922_, 1);
lean_ctor_set(v___x_922_, 1, v___x_928_);
lean_ctor_set(v___x_922_, 0, v___x_927_);
v___x_930_ = v___x_922_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v___x_928_);
v___x_930_ = v_reuseFailAlloc_935_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_925_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2));
v___x_933_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_931_, v___x_932_);
v___x_934_ = l_Lean_Json_mkObj(v___x_933_);
lean_dec(v___x_933_);
return v___x_934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2(lean_object* v_x_941_){
_start:
{
if (lean_obj_tag(v_x_941_) == 0)
{
lean_object* v___x_942_; 
v___x_942_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2___closed__0));
return v___x_942_;
}
else
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_Lsp_instFromJsonLogConfig_fromJson(v_x_941_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_960_; 
v_a_952_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_960_ == 0)
{
v___x_954_ = v___x_943_;
v_isShared_955_ = v_isSharedCheck_960_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_943_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_960_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_956_, 0, v_a_952_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_956_);
v___x_958_ = v___x_954_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1(lean_object* v_j_961_, lean_object* v_k_962_){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = l_Lean_Json_getObjValD(v_j_961_, v_k_962_);
v___x_964_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2(v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1___boxed(lean_object* v_j_965_, lean_object* v_k_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1(v_j_965_, v_k_966_);
lean_dec_ref(v_k_966_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0(lean_object* v_x_970_){
_start:
{
if (lean_obj_tag(v_x_970_) == 0)
{
lean_object* v___x_971_; 
v___x_971_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___closed__0));
return v___x_971_;
}
else
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_Json_getBool_x3f(v_x_970_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_989_; 
v_a_981_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_989_ == 0)
{
v___x_983_ = v___x_972_;
v_isShared_984_ = v_isSharedCheck_989_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_972_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_989_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_985_, 0, v_a_981_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_985_);
v___x_987_ = v___x_983_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___boxed(lean_object* v_x_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0(v_x_990_);
lean_dec(v_x_990_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0(lean_object* v_j_992_, lean_object* v_k_993_){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = l_Lean_Json_getObjValD(v_j_992_, v_k_993_);
v___x_995_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0(v___x_994_);
lean_dec(v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0___boxed(lean_object* v_j_996_, lean_object* v_k_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0(v_j_996_, v_k_997_);
lean_dec_ref(v_k_997_);
return v_res_998_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = 1;
v___x_1005_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1));
v___x_1006_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1005_, v___x_1004_);
return v___x_1006_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5));
v___x_1008_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2);
v___x_1009_ = lean_string_append(v___x_1008_, v___x_1007_);
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1013_ = 1;
v___x_1014_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__5));
v___x_1015_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1014_, v___x_1013_);
return v___x_1015_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1016_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6);
v___x_1017_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3);
v___x_1018_ = lean_string_append(v___x_1017_, v___x_1016_);
return v___x_1018_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_1020_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7);
v___x_1021_ = lean_string_append(v___x_1020_, v___x_1019_);
return v___x_1021_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11(void){
_start:
{
uint8_t v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = 1;
v___x_1026_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__10));
v___x_1027_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1026_, v___x_1025_);
return v___x_1027_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11);
v___x_1029_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3);
v___x_1030_ = lean_string_append(v___x_1029_, v___x_1028_);
return v___x_1030_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1031_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_1032_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12);
v___x_1033_ = lean_string_append(v___x_1032_, v___x_1031_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializationOptions_fromJson(lean_object* v_json_1034_){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__0));
lean_inc(v_json_1034_);
v___x_1036_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0(v_json_1034_, v___x_1035_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1046_; 
lean_dec(v_json_1034_);
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1039_ = v___x_1036_;
v_isShared_1040_ = v_isSharedCheck_1046_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1036_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1046_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1041_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8);
v___x_1042_ = lean_string_append(v___x_1041_, v_a_1037_);
lean_dec(v_a_1037_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 0, v___x_1042_);
v___x_1044_ = v___x_1039_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
else
{
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec(v_json_1034_);
v_a_1047_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1036_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1036_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
lean_ctor_set_tag(v___x_1049_, 0);
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v_a_1055_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v___x_1036_, 1);
v___x_1056_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__1));
v___x_1057_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1(v_json_1034_, v___x_1056_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1067_; 
lean_dec(v_a_1055_);
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1060_ = v___x_1057_;
v_isShared_1061_ = v_isSharedCheck_1067_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1057_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1067_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1062_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13);
v___x_1063_ = lean_string_append(v___x_1062_, v_a_1058_);
lean_dec(v_a_1058_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v___x_1063_);
v___x_1065_ = v___x_1060_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
else
{
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_dec(v_a_1055_);
v_a_1068_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1057_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1057_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set_tag(v___x_1070_, 0);
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1084_; 
v_a_1076_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1078_ = v___x_1057_;
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1057_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1080_, 0, v_a_1055_);
lean_ctor_set(v___x_1080_, 1, v_a_1076_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1080_);
v___x_1082_ = v___x_1078_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__0(lean_object* v_k_1087_, lean_object* v_x_1088_){
_start:
{
if (lean_obj_tag(v_x_1088_) == 0)
{
lean_object* v___x_1089_; 
lean_dec_ref(v_k_1087_);
v___x_1089_ = lean_box(0);
return v___x_1089_;
}
else
{
lean_object* v_val_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1101_; 
v_val_1090_ = lean_ctor_get(v_x_1088_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_x_1088_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1092_ = v_x_1088_;
v_isShared_1093_ = v_isSharedCheck_1101_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_val_1090_);
lean_dec(v_x_1088_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1101_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1094_ = l_Lean_JsonNumber_fromInt(v_val_1090_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set_tag(v___x_1092_, 2);
lean_ctor_set(v___x_1092_, 0, v___x_1094_);
v___x_1096_ = v___x_1092_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1097_, 0, v_k_1087_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = lean_box(0);
v___x_1099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
return v___x_1099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__1(lean_object* v_k_1102_, lean_object* v_x_1103_){
_start:
{
if (lean_obj_tag(v_x_1103_) == 0)
{
lean_object* v___x_1104_; 
lean_dec_ref(v_k_1102_);
v___x_1104_ = lean_box(0);
return v___x_1104_;
}
else
{
lean_object* v_val_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v_val_1105_ = lean_ctor_get(v_x_1103_, 0);
lean_inc(v_val_1105_);
lean_dec_ref_known(v_x_1103_, 1);
v___x_1106_ = l_Lean_Lsp_instToJsonClientInfo_toJson(v_val_1105_);
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v_k_1102_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = lean_box(0);
v___x_1109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1107_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
return v___x_1109_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__2(lean_object* v_k_1110_, lean_object* v_x_1111_){
_start:
{
if (lean_obj_tag(v_x_1111_) == 0)
{
lean_object* v___x_1112_; 
lean_dec_ref(v_k_1110_);
v___x_1112_ = lean_box(0);
return v___x_1112_;
}
else
{
lean_object* v_val_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_val_1113_ = lean_ctor_get(v_x_1111_, 0);
lean_inc(v_val_1113_);
lean_dec_ref_known(v_x_1111_, 1);
v___x_1114_ = l_Lean_Lsp_instToJsonInitializationOptions_toJson(v_val_1113_);
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v_k_1110_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
v___x_1116_ = lean_box(0);
v___x_1117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1115_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
return v___x_1117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4(size_t v_sz_1118_, size_t v_i_1119_, lean_object* v_bs_1120_){
_start:
{
uint8_t v___x_1121_; 
v___x_1121_ = lean_usize_dec_lt(v_i_1119_, v_sz_1118_);
if (v___x_1121_ == 0)
{
return v_bs_1120_;
}
else
{
lean_object* v_v_1122_; lean_object* v___x_1123_; lean_object* v_bs_x27_1124_; lean_object* v___x_1125_; size_t v___x_1126_; size_t v___x_1127_; lean_object* v___x_1128_; 
v_v_1122_ = lean_array_uget(v_bs_1120_, v_i_1119_);
v___x_1123_ = lean_unsigned_to_nat(0u);
v_bs_x27_1124_ = lean_array_uset(v_bs_1120_, v_i_1119_, v___x_1123_);
v___x_1125_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson(v_v_1122_);
v___x_1126_ = ((size_t)1ULL);
v___x_1127_ = lean_usize_add(v_i_1119_, v___x_1126_);
v___x_1128_ = lean_array_uset(v_bs_x27_1124_, v_i_1119_, v___x_1125_);
v_i_1119_ = v___x_1127_;
v_bs_1120_ = v___x_1128_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_1130_, lean_object* v_i_1131_, lean_object* v_bs_1132_){
_start:
{
size_t v_sz_boxed_1133_; size_t v_i_boxed_1134_; lean_object* v_res_1135_; 
v_sz_boxed_1133_ = lean_unbox_usize(v_sz_1130_);
lean_dec(v_sz_1130_);
v_i_boxed_1134_ = lean_unbox_usize(v_i_1131_);
lean_dec(v_i_1131_);
v_res_1135_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4(v_sz_boxed_1133_, v_i_boxed_1134_, v_bs_1132_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3(lean_object* v_a_1136_){
_start:
{
size_t v_sz_1137_; size_t v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v_sz_1137_ = lean_array_size(v_a_1136_);
v___x_1138_ = ((size_t)0ULL);
v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4(v_sz_1137_, v___x_1138_, v_a_1136_);
v___x_1140_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3(lean_object* v_k_1141_, lean_object* v_x_1142_){
_start:
{
if (lean_obj_tag(v_x_1142_) == 0)
{
lean_object* v___x_1143_; 
lean_dec_ref(v_k_1141_);
v___x_1143_ = lean_box(0);
return v___x_1143_;
}
else
{
lean_object* v_val_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v_val_1144_ = lean_ctor_get(v_x_1142_, 0);
lean_inc(v_val_1144_);
lean_dec_ref_known(v_x_1142_, 1);
v___x_1145_ = l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3(v_val_1144_);
v___x_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1146_, 0, v_k_1141_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = lean_box(0);
v___x_1148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1146_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
return v___x_1148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonInitializeParams_toJson(lean_object* v_x_1156_){
_start:
{
lean_object* v_processId_x3f_1157_; lean_object* v_clientInfo_x3f_1158_; lean_object* v_rootUri_x3f_1159_; lean_object* v_initializationOptions_x3f_1160_; lean_object* v_capabilities_1161_; uint8_t v_trace_1162_; lean_object* v_workspaceFolders_x3f_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___y_1179_; 
v_processId_x3f_1157_ = lean_ctor_get(v_x_1156_, 0);
lean_inc(v_processId_x3f_1157_);
v_clientInfo_x3f_1158_ = lean_ctor_get(v_x_1156_, 1);
lean_inc(v_clientInfo_x3f_1158_);
v_rootUri_x3f_1159_ = lean_ctor_get(v_x_1156_, 2);
lean_inc(v_rootUri_x3f_1159_);
v_initializationOptions_x3f_1160_ = lean_ctor_get(v_x_1156_, 3);
lean_inc(v_initializationOptions_x3f_1160_);
v_capabilities_1161_ = lean_ctor_get(v_x_1156_, 4);
lean_inc_ref(v_capabilities_1161_);
v_trace_1162_ = lean_ctor_get_uint8(v_x_1156_, sizeof(void*)*6);
v_workspaceFolders_x3f_1163_ = lean_ctor_get(v_x_1156_, 5);
lean_inc(v_workspaceFolders_x3f_1163_);
lean_dec_ref(v_x_1156_);
v___x_1164_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__0));
v___x_1165_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__0(v___x_1164_, v_processId_x3f_1157_);
v___x_1166_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__1));
v___x_1167_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__1(v___x_1166_, v_clientInfo_x3f_1158_);
v___x_1168_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__2));
v___x_1169_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__0(v___x_1168_, v_rootUri_x3f_1159_);
v___x_1170_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__3));
v___x_1171_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__2(v___x_1170_, v_initializationOptions_x3f_1160_);
v___x_1172_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4));
v___x_1173_ = l_Lean_Lsp_instToJsonClientCapabilities_toJson(v_capabilities_1161_);
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = lean_box(0);
v___x_1176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1174_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__5));
switch(v_trace_1162_)
{
case 0:
{
lean_object* v___x_1194_; 
v___x_1194_ = ((lean_object*)(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__0));
v___y_1179_ = v___x_1194_;
goto v___jp_1178_;
}
case 1:
{
lean_object* v___x_1195_; 
v___x_1195_ = ((lean_object*)(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__1));
v___y_1179_ = v___x_1195_;
goto v___jp_1178_;
}
default: 
{
lean_object* v___x_1196_; 
v___x_1196_ = ((lean_object*)(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__2));
v___y_1179_ = v___x_1196_;
goto v___jp_1178_;
}
}
v___jp_1178_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_inc(v___y_1179_);
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1177_);
lean_ctor_set(v___x_1180_, 1, v___y_1179_);
v___x_1181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
lean_ctor_set(v___x_1181_, 1, v___x_1175_);
v___x_1182_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__6));
v___x_1183_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3(v___x_1182_, v_workspaceFolders_x3f_1163_);
v___x_1184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v___x_1175_);
v___x_1185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1181_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1176_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
v___x_1187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1171_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1169_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___x_1189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1167_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1165_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
v___x_1191_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2));
v___x_1192_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_1190_, v___x_1191_);
v___x_1193_ = l_Lean_Json_mkObj(v___x_1192_);
lean_dec(v___x_1192_);
return v___x_1193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializeParams___lam__0(lean_object* v___x_1199_, lean_object* v___x_1200_, lean_object* v___x_1201_, lean_object* v___x_1202_, lean_object* v___x_1203_, lean_object* v___x_1204_, lean_object* v___f_1205_, lean_object* v_j_1206_){
_start:
{
lean_object* v___x_1207_; lean_object* v_processId_x3f_1208_; lean_object* v___x_1209_; lean_object* v_clientInfo_x3f_1210_; lean_object* v___x_1211_; lean_object* v_rootUri_x3f_1212_; lean_object* v___x_1213_; lean_object* v_initializationOptions_x3f_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1207_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__0));
lean_inc_n(v_j_1206_, 5);
v_processId_x3f_1208_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1206_, v___x_1199_, v___x_1207_);
v___x_1209_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__1));
v_clientInfo_x3f_1210_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1206_, v___x_1200_, v___x_1209_);
v___x_1211_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__2));
v_rootUri_x3f_1212_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1206_, v___x_1201_, v___x_1211_);
v___x_1213_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__3));
v_initializationOptions_x3f_1214_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1206_, v___x_1202_, v___x_1213_);
v___x_1215_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4));
v___x_1216_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1206_, v___x_1203_, v___x_1215_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec_ref(v_initializationOptions_x3f_1214_);
lean_dec_ref(v_rootUri_x3f_1212_);
lean_dec_ref(v_clientInfo_x3f_1210_);
lean_dec_ref(v_processId_x3f_1208_);
lean_dec(v_j_1206_);
lean_dec_ref(v___f_1205_);
lean_dec_ref(v___x_1204_);
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1216_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1216_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1316_; 
v_a_1225_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1227_ = v___x_1216_;
v_isShared_1228_ = v_isSharedCheck_1316_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1216_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1316_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; uint8_t v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; uint8_t v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1257_; lean_object* v___y_1258_; uint8_t v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1272_; uint8_t v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; uint8_t v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; uint8_t v___y_1299_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__5));
lean_inc(v_j_1206_);
v___x_1312_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1206_, v___f_1205_, v___x_1311_);
if (lean_obj_tag(v___x_1312_) == 0)
{
uint8_t v___x_1313_; 
lean_dec_ref_known(v___x_1312_, 1);
v___x_1313_ = 0;
v___y_1299_ = v___x_1313_;
goto v___jp_1298_;
}
else
{
lean_object* v_a_1314_; uint8_t v___x_1315_; 
v_a_1314_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_a_1314_);
lean_dec_ref_known(v___x_1312_, 1);
v___x_1315_ = lean_unbox(v_a_1314_);
lean_dec(v_a_1314_);
v___y_1299_ = v___x_1315_;
goto v___jp_1298_;
}
v___jp_1229_:
{
lean_object* v___x_1236_; lean_object* v___x_1238_; 
v___x_1236_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1236_, 0, v___y_1232_);
lean_ctor_set(v___x_1236_, 1, v___y_1231_);
lean_ctor_set(v___x_1236_, 2, v___y_1230_);
lean_ctor_set(v___x_1236_, 3, v___y_1233_);
lean_ctor_set(v___x_1236_, 4, v_a_1225_);
lean_ctor_set(v___x_1236_, 5, v___y_1235_);
lean_ctor_set_uint8(v___x_1236_, sizeof(void*)*6, v___y_1234_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1236_);
v___x_1238_ = v___x_1227_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
v___jp_1240_:
{
if (lean_obj_tag(v___y_1245_) == 0)
{
lean_object* v___x_1247_; 
lean_dec_ref_known(v___y_1245_, 1);
v___x_1247_ = lean_box(0);
v___y_1230_ = v___y_1241_;
v___y_1231_ = v___y_1243_;
v___y_1232_ = v___y_1242_;
v___y_1233_ = v___y_1246_;
v___y_1234_ = v___y_1244_;
v___y_1235_ = v___x_1247_;
goto v___jp_1229_;
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
v_a_1248_ = lean_ctor_get(v___y_1245_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___y_1245_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___y_1245_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___y_1245_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
v___y_1230_ = v___y_1241_;
v___y_1231_ = v___y_1243_;
v___y_1232_ = v___y_1242_;
v___y_1233_ = v___y_1246_;
v___y_1234_ = v___y_1244_;
v___y_1235_ = v___x_1253_;
goto v___jp_1229_;
}
}
}
}
v___jp_1256_:
{
if (lean_obj_tag(v_initializationOptions_x3f_1214_) == 0)
{
lean_object* v___x_1262_; 
lean_dec_ref_known(v_initializationOptions_x3f_1214_, 1);
v___x_1262_ = lean_box(0);
v___y_1241_ = v___y_1261_;
v___y_1242_ = v___y_1258_;
v___y_1243_ = v___y_1257_;
v___y_1244_ = v___y_1259_;
v___y_1245_ = v___y_1260_;
v___y_1246_ = v___x_1262_;
goto v___jp_1240_;
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
v_a_1263_ = lean_ctor_get(v_initializationOptions_x3f_1214_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_initializationOptions_x3f_1214_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v_initializationOptions_x3f_1214_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v_initializationOptions_x3f_1214_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
v___y_1241_ = v___y_1261_;
v___y_1242_ = v___y_1258_;
v___y_1243_ = v___y_1257_;
v___y_1244_ = v___y_1259_;
v___y_1245_ = v___y_1260_;
v___y_1246_ = v___x_1268_;
goto v___jp_1240_;
}
}
}
}
v___jp_1271_:
{
if (lean_obj_tag(v_rootUri_x3f_1212_) == 0)
{
lean_object* v___x_1276_; 
lean_dec_ref_known(v_rootUri_x3f_1212_, 1);
v___x_1276_ = lean_box(0);
v___y_1257_ = v___y_1275_;
v___y_1258_ = v___y_1272_;
v___y_1259_ = v___y_1273_;
v___y_1260_ = v___y_1274_;
v___y_1261_ = v___x_1276_;
goto v___jp_1256_;
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
v_a_1277_ = lean_ctor_get(v_rootUri_x3f_1212_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_rootUri_x3f_1212_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v_rootUri_x3f_1212_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v_rootUri_x3f_1212_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
v___y_1257_ = v___y_1275_;
v___y_1258_ = v___y_1272_;
v___y_1259_ = v___y_1273_;
v___y_1260_ = v___y_1274_;
v___y_1261_ = v___x_1282_;
goto v___jp_1256_;
}
}
}
}
v___jp_1285_:
{
if (lean_obj_tag(v_clientInfo_x3f_1210_) == 0)
{
lean_object* v___x_1289_; 
lean_dec_ref_known(v_clientInfo_x3f_1210_, 1);
v___x_1289_ = lean_box(0);
v___y_1272_ = v___y_1288_;
v___y_1273_ = v___y_1286_;
v___y_1274_ = v___y_1287_;
v___y_1275_ = v___x_1289_;
goto v___jp_1271_;
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
v_a_1290_ = lean_ctor_get(v_clientInfo_x3f_1210_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_clientInfo_x3f_1210_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v_clientInfo_x3f_1210_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v_clientInfo_x3f_1210_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
v___y_1272_ = v___y_1288_;
v___y_1273_ = v___y_1286_;
v___y_1274_ = v___y_1287_;
v___y_1275_ = v___x_1295_;
goto v___jp_1271_;
}
}
}
}
v___jp_1298_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__6));
v___x_1301_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1206_, v___x_1204_, v___x_1300_);
if (lean_obj_tag(v_processId_x3f_1208_) == 0)
{
lean_object* v___x_1302_; 
lean_dec_ref_known(v_processId_x3f_1208_, 1);
v___x_1302_ = lean_box(0);
v___y_1286_ = v___y_1299_;
v___y_1287_ = v___x_1301_;
v___y_1288_ = v___x_1302_;
goto v___jp_1285_;
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
v_a_1303_ = lean_ctor_get(v_processId_x3f_1208_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_processId_x3f_1208_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v_processId_x3f_1208_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v_processId_x3f_1208_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
v___y_1286_ = v___y_1299_;
v___y_1287_ = v___x_1301_;
v___y_1288_ = v___x_1308_;
goto v___jp_1285_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializedParams___lam__0(lean_object* v_x_1334_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializedParams___lam__0___closed__0));
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializedParams___lam__0___boxed(lean_object* v_x_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_Lsp_instFromJsonInitializedParams___lam__0(v_x_1336_);
lean_dec(v_x_1336_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonInitializedParams___lam__0(lean_object* v_x_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_box(0);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonServerInfo_toJson(lean_object* v_x_1344_){
_start:
{
lean_object* v_name_1345_; lean_object* v_version_x3f_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1364_; 
v_name_1345_ = lean_ctor_get(v_x_1344_, 0);
v_version_x3f_1346_ = lean_ctor_get(v_x_1344_, 1);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_x_1344_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1348_ = v_x_1344_;
v_isShared_1349_ = v_isSharedCheck_1364_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_version_x3f_1346_);
lean_inc(v_name_1345_);
lean_dec(v_x_1344_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1364_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1350_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0));
v___x_1351_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1351_, 0, v_name_1345_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 1, v___x_1351_);
lean_ctor_set(v___x_1348_, 0, v___x_1350_);
v___x_1353_ = v___x_1348_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1354_ = lean_box(0);
v___x_1355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1353_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1));
v___x_1357_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__0(v___x_1356_, v_version_x3f_1346_);
v___x_1358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
lean_ctor_set(v___x_1358_, 1, v___x_1354_);
v___x_1359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1355_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2));
v___x_1361_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_1359_, v___x_1360_);
v___x_1362_ = l_Lean_Json_mkObj(v___x_1361_);
lean_dec(v___x_1361_);
return v___x_1362_;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1372_ = 1;
v___x_1373_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1));
v___x_1374_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1373_, v___x_1372_);
return v___x_1374_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5));
v___x_1376_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2);
v___x_1377_ = lean_string_append(v___x_1376_, v___x_1375_);
return v___x_1377_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1378_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8, &l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8);
v___x_1379_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3);
v___x_1380_ = lean_string_append(v___x_1379_, v___x_1378_);
return v___x_1380_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1381_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_1382_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4);
v___x_1383_ = lean_string_append(v___x_1382_, v___x_1381_);
return v___x_1383_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1384_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14, &l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14);
v___x_1385_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3);
v___x_1386_ = lean_string_append(v___x_1385_, v___x_1384_);
return v___x_1386_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1387_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_1388_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6);
v___x_1389_ = lean_string_append(v___x_1388_, v___x_1387_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonServerInfo_fromJson(lean_object* v_json_1390_){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0));
lean_inc(v_json_1390_);
v___x_1392_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__0(v_json_1390_, v___x_1391_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1402_; 
lean_dec(v_json_1390_);
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1395_ = v___x_1392_;
v_isShared_1396_ = v_isSharedCheck_1402_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1392_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1402_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1400_; 
v___x_1397_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5);
v___x_1398_ = lean_string_append(v___x_1397_, v_a_1393_);
lean_dec(v_a_1393_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1398_);
v___x_1400_ = v___x_1395_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1398_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
else
{
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
lean_dec(v_json_1390_);
v_a_1403_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1392_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1392_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
lean_ctor_set_tag(v___x_1405_, 0);
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v_a_1411_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1411_);
lean_dec_ref_known(v___x_1392_, 1);
v___x_1412_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1));
v___x_1413_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1(v_json_1390_, v___x_1412_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1423_; 
lean_dec(v_a_1411_);
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1423_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1423_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1418_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7);
v___x_1419_ = lean_string_append(v___x_1418_, v_a_1414_);
lean_dec(v_a_1414_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1419_);
v___x_1421_ = v___x_1416_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
else
{
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
lean_dec(v_a_1411_);
v_a_1424_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1413_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1413_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
lean_ctor_set_tag(v___x_1426_, 0);
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1440_; 
v_a_1432_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1434_ = v___x_1413_;
v_isShared_1435_ = v_isSharedCheck_1440_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1413_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1440_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1436_, 0, v_a_1411_);
lean_ctor_set(v___x_1436_, 1, v_a_1432_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1436_);
v___x_1438_ = v___x_1434_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeResult_toJson_spec__0(lean_object* v_k_1443_, lean_object* v_x_1444_){
_start:
{
if (lean_obj_tag(v_x_1444_) == 0)
{
lean_object* v___x_1445_; 
lean_dec_ref(v_k_1443_);
v___x_1445_ = lean_box(0);
return v___x_1445_;
}
else
{
lean_object* v_val_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v_val_1446_ = lean_ctor_get(v_x_1444_, 0);
lean_inc(v_val_1446_);
lean_dec_ref_known(v_x_1444_, 1);
v___x_1447_ = l_Lean_Lsp_instToJsonServerInfo_toJson(v_val_1446_);
v___x_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1448_, 0, v_k_1443_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
v___x_1449_ = lean_box(0);
v___x_1450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1448_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
return v___x_1450_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonInitializeResult_toJson(lean_object* v_x_1452_){
_start:
{
lean_object* v_capabilities_1453_; lean_object* v_serverInfo_x3f_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1472_; 
v_capabilities_1453_ = lean_ctor_get(v_x_1452_, 0);
v_serverInfo_x3f_1454_ = lean_ctor_get(v_x_1452_, 1);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_x_1452_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1456_ = v_x_1452_;
v_isShared_1457_ = v_isSharedCheck_1472_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_serverInfo_x3f_1454_);
lean_inc(v_capabilities_1453_);
lean_dec(v_x_1452_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1472_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1458_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4));
v___x_1459_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson(v_capabilities_1453_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 1, v___x_1459_);
lean_ctor_set(v___x_1456_, 0, v___x_1458_);
v___x_1461_ = v___x_1456_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1462_ = lean_box(0);
v___x_1463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1461_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeResult_toJson___closed__0));
v___x_1465_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeResult_toJson_spec__0(v___x_1464_, v_serverInfo_x3f_1454_);
v___x_1466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
lean_ctor_set(v___x_1466_, 1, v___x_1462_);
v___x_1467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1463_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2));
v___x_1469_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_1467_, v___x_1468_);
v___x_1470_ = l_Lean_Json_mkObj(v___x_1469_);
lean_dec(v___x_1469_);
return v___x_1470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0(lean_object* v_j_1475_, lean_object* v_k_1476_){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = l_Lean_Json_getObjValD(v_j_1475_, v_k_1476_);
v___x_1478_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson(v___x_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0___boxed(lean_object* v_j_1479_, lean_object* v_k_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0(v_j_1479_, v_k_1480_);
lean_dec_ref(v_k_1480_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1(lean_object* v_x_1484_){
_start:
{
if (lean_obj_tag(v_x_1484_) == 0)
{
lean_object* v___x_1485_; 
v___x_1485_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1___closed__0));
return v___x_1485_;
}
else
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_Lsp_instFromJsonServerInfo_fromJson(v_x_1484_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1486_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1486_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1503_; 
v_a_1495_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1497_ = v___x_1486_;
v_isShared_1498_ = v_isSharedCheck_1503_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1486_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1503_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1499_; lean_object* v___x_1501_; 
v___x_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1499_, 0, v_a_1495_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v___x_1499_);
v___x_1501_ = v___x_1497_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1(lean_object* v_j_1504_, lean_object* v_k_1505_){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = l_Lean_Json_getObjValD(v_j_1504_, v_k_1505_);
v___x_1507_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1(v___x_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1___boxed(lean_object* v_j_1508_, lean_object* v_k_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1(v_j_1508_, v_k_1509_);
lean_dec_ref(v_k_1509_);
return v_res_1510_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = 1;
v___x_1517_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1));
v___x_1518_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1517_, v___x_1516_);
return v___x_1518_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1519_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5));
v___x_1520_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2);
v___x_1521_ = lean_string_append(v___x_1520_, v___x_1519_);
return v___x_1521_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1524_ = 1;
v___x_1525_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__4));
v___x_1526_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1525_, v___x_1524_);
return v___x_1526_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1527_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5);
v___x_1528_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3);
v___x_1529_ = lean_string_append(v___x_1528_, v___x_1527_);
return v___x_1529_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1530_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_1531_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6);
v___x_1532_ = lean_string_append(v___x_1531_, v___x_1530_);
return v___x_1532_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10(void){
_start:
{
uint8_t v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1536_ = 1;
v___x_1537_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__9));
v___x_1538_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1537_, v___x_1536_);
return v___x_1538_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1539_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10);
v___x_1540_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3);
v___x_1541_ = lean_string_append(v___x_1540_, v___x_1539_);
return v___x_1541_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1542_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_1543_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11);
v___x_1544_ = lean_string_append(v___x_1543_, v___x_1542_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializeResult_fromJson(lean_object* v_json_1545_){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4));
lean_inc(v_json_1545_);
v___x_1547_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0(v_json_1545_, v___x_1546_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1557_; 
lean_dec(v_json_1545_);
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1557_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1557_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1555_; 
v___x_1552_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7);
v___x_1553_ = lean_string_append(v___x_1552_, v_a_1548_);
lean_dec(v_a_1548_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1553_);
v___x_1555_ = v___x_1550_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
else
{
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec(v_json_1545_);
v_a_1558_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1547_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1547_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
lean_ctor_set_tag(v___x_1560_, 0);
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v_a_1566_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1547_, 1);
v___x_1567_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeResult_toJson___closed__0));
v___x_1568_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1(v_json_1545_, v___x_1567_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1578_; 
lean_dec(v_a_1566_);
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1571_ = v___x_1568_;
v_isShared_1572_ = v_isSharedCheck_1578_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1568_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1578_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1573_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12);
v___x_1574_ = lean_string_append(v___x_1573_, v_a_1569_);
lean_dec(v_a_1569_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 0, v___x_1574_);
v___x_1576_ = v___x_1571_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
else
{
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec(v_a_1566_);
v_a_1579_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1568_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1568_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
lean_ctor_set_tag(v___x_1581_, 0);
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1595_; 
v_a_1587_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1589_ = v___x_1568_;
v_isShared_1590_ = v_isSharedCheck_1595_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1568_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1595_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1591_, 0, v_a_1566_);
lean_ctor_set(v___x_1591_, 1, v_a_1587_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v___x_1591_);
v___x_1593_ = v___x_1589_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
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
