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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson(lean_object*);
lean_object* l_Array_fromJson_x3f(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__0_value;
static lean_once_cell_t l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1;
static lean_once_cell_t l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2;
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__4_value)}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__3 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__3_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3(lean_object*);
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
static const lean_closure_object l_Lean_Lsp_instFromJsonInitializeParams___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonInitializeParams___closed__3_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonInitializeParams___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializeParams___closed__4_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonInitializeParams___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonInitializeParams___lam__0, .m_arity = 8, .m_num_fixed = 7, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonInitializeParams___closed__0_value),((lean_object*)&l_Lean_Lsp_instFromJsonClientInfo___closed__0_value),((lean_object*)&l_Lean_Lsp_instFromJsonInitializeParams___closed__1_value),((lean_object*)&l_Lean_Lsp_instFromJsonInitializationOptions___closed__0_value),((lean_object*)&l_Lean_Lsp_instFromJsonInitializeParams___closed__2_value),((lean_object*)&l_Lean_Lsp_instFromJsonInitializeParams___closed__4_value),((lean_object*)&l_Lean_Lsp_instFromJsonTrace___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonInitializeParams___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializeParams___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonInitializeParams = (const lean_object*)&l_Lean_Lsp_instFromJsonInitializeParams___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_InitializedParams_toCtorIdx(lean_object*);
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
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1(lean_object*);
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
lean_dec_ref(v_a_15_);
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
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1(lean_object* v_x_58_){
_start:
{
if (lean_obj_tag(v_x_58_) == 0)
{
lean_object* v___x_59_; 
v___x_59_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1___closed__0));
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
v___x_81_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1(v___x_80_);
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
lean_dec_ref(v___x_125_);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_toCtorIdx(uint8_t v_x_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Lsp_Trace_ctorIdx(v_x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_toCtorIdx___boxed(lean_object* v_x_185_){
_start:
{
uint8_t v_x_4__boxed_186_; lean_object* v_res_187_; 
v_x_4__boxed_186_ = lean_unbox(v_x_185_);
v_res_187_ = l_Lean_Lsp_Trace_toCtorIdx(v_x_4__boxed_186_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorElim___redArg(lean_object* v_k_188_){
_start:
{
lean_inc(v_k_188_);
return v_k_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorElim___redArg___boxed(lean_object* v_k_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_Lsp_Trace_ctorElim___redArg(v_k_189_);
lean_dec(v_k_189_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorElim(lean_object* v_motive_191_, lean_object* v_ctorIdx_192_, uint8_t v_t_193_, lean_object* v_h_194_, lean_object* v_k_195_){
_start:
{
lean_inc(v_k_195_);
return v_k_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorElim___boxed(lean_object* v_motive_196_, lean_object* v_ctorIdx_197_, lean_object* v_t_198_, lean_object* v_h_199_, lean_object* v_k_200_){
_start:
{
uint8_t v_t_boxed_201_; lean_object* v_res_202_; 
v_t_boxed_201_ = lean_unbox(v_t_198_);
v_res_202_ = l_Lean_Lsp_Trace_ctorElim(v_motive_196_, v_ctorIdx_197_, v_t_boxed_201_, v_h_199_, v_k_200_);
lean_dec(v_k_200_);
lean_dec(v_ctorIdx_197_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_off_elim___redArg(lean_object* v_off_203_){
_start:
{
lean_inc(v_off_203_);
return v_off_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_off_elim___redArg___boxed(lean_object* v_off_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Lsp_Trace_off_elim___redArg(v_off_204_);
lean_dec(v_off_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_off_elim(lean_object* v_motive_206_, uint8_t v_t_207_, lean_object* v_h_208_, lean_object* v_off_209_){
_start:
{
lean_inc(v_off_209_);
return v_off_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_off_elim___boxed(lean_object* v_motive_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_off_213_){
_start:
{
uint8_t v_t_boxed_214_; lean_object* v_res_215_; 
v_t_boxed_214_ = lean_unbox(v_t_211_);
v_res_215_ = l_Lean_Lsp_Trace_off_elim(v_motive_210_, v_t_boxed_214_, v_h_212_, v_off_213_);
lean_dec(v_off_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_messages_elim___redArg(lean_object* v_messages_216_){
_start:
{
lean_inc(v_messages_216_);
return v_messages_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_messages_elim___redArg___boxed(lean_object* v_messages_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_Lsp_Trace_messages_elim___redArg(v_messages_217_);
lean_dec(v_messages_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_messages_elim(lean_object* v_motive_219_, uint8_t v_t_220_, lean_object* v_h_221_, lean_object* v_messages_222_){
_start:
{
lean_inc(v_messages_222_);
return v_messages_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_messages_elim___boxed(lean_object* v_motive_223_, lean_object* v_t_224_, lean_object* v_h_225_, lean_object* v_messages_226_){
_start:
{
uint8_t v_t_boxed_227_; lean_object* v_res_228_; 
v_t_boxed_227_ = lean_unbox(v_t_224_);
v_res_228_ = l_Lean_Lsp_Trace_messages_elim(v_motive_223_, v_t_boxed_227_, v_h_225_, v_messages_226_);
lean_dec(v_messages_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_verbose_elim___redArg(lean_object* v_verbose_229_){
_start:
{
lean_inc(v_verbose_229_);
return v_verbose_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_verbose_elim___redArg___boxed(lean_object* v_verbose_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Lsp_Trace_verbose_elim___redArg(v_verbose_230_);
lean_dec(v_verbose_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_verbose_elim(lean_object* v_motive_232_, uint8_t v_t_233_, lean_object* v_h_234_, lean_object* v_verbose_235_){
_start:
{
lean_inc(v_verbose_235_);
return v_verbose_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_verbose_elim___boxed(lean_object* v_motive_236_, lean_object* v_t_237_, lean_object* v_h_238_, lean_object* v_verbose_239_){
_start:
{
uint8_t v_t_boxed_240_; lean_object* v_res_241_; 
v_t_boxed_240_ = lean_unbox(v_t_237_);
v_res_241_ = l_Lean_Lsp_Trace_verbose_elim(v_motive_236_, v_t_boxed_240_, v_h_238_, v_verbose_239_);
lean_dec(v_verbose_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTrace___lam__0(lean_object* v_j_257_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Json_getStr_x3f(v_j_257_);
if (lean_obj_tag(v___x_260_) == 1)
{
lean_object* v_a_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_261_);
lean_dec_ref(v___x_260_);
v___x_262_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__2));
v___x_263_ = lean_string_dec_eq(v_a_261_, v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__3));
v___x_265_ = lean_string_dec_eq(v_a_261_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__4));
v___x_267_ = lean_string_dec_eq(v_a_261_, v___x_266_);
lean_dec(v_a_261_);
if (v___x_267_ == 0)
{
goto v___jp_258_;
}
else
{
lean_object* v___x_268_; 
v___x_268_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__5));
return v___x_268_;
}
}
else
{
lean_object* v___x_269_; 
lean_dec(v_a_261_);
v___x_269_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__6));
return v___x_269_;
}
}
else
{
lean_object* v___x_270_; 
lean_dec(v_a_261_);
v___x_270_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__7));
return v___x_270_;
}
}
else
{
lean_dec_ref(v___x_260_);
goto v___jp_258_;
}
v___jp_258_:
{
lean_object* v___x_259_; 
v___x_259_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__1));
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_hasToJson___lam__0(uint8_t v_x_279_){
_start:
{
switch(v_x_279_)
{
case 0:
{
lean_object* v___x_280_; 
v___x_280_ = ((lean_object*)(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__0));
return v___x_280_;
}
case 1:
{
lean_object* v___x_281_; 
v___x_281_ = ((lean_object*)(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__1));
return v___x_281_;
}
default: 
{
lean_object* v___x_282_; 
v___x_282_ = ((lean_object*)(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__2));
return v___x_282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_hasToJson___lam__0___boxed(lean_object* v_x_283_){
_start:
{
uint8_t v_x_54__boxed_284_; lean_object* v_res_285_; 
v_x_54__boxed_284_ = lean_unbox(v_x_283_);
v_res_285_ = l_Lean_Lsp_Trace_hasToJson___lam__0(v_x_54__boxed_284_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__0(lean_object* v_x1_288_, lean_object* v_x2_289_, lean_object* v_x3_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = lean_array_push(v_x1_288_, v_x2_289_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__1(lean_object* v_inst_292_, lean_object* v_x_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = lean_apply_1(v_inst_292_, v_x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__2(lean_object* v___x_295_, lean_object* v___f_296_, lean_object* v_acc_297_, lean_object* v_l_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_295_, v___f_296_, v_acc_297_, v_l_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__3(lean_object* v___f_319_, lean_object* v___f_320_, lean_object* v_s_321_){
_start:
{
lean_object* v___y_323_; lean_object* v_size_329_; lean_object* v_buckets_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v_size_329_ = lean_ctor_get(v_s_321_, 0);
lean_inc(v_size_329_);
v_buckets_330_ = lean_ctor_get(v_s_321_, 1);
lean_inc_ref(v_buckets_330_);
lean_dec_ref(v_s_321_);
v___x_331_ = lean_mk_empty_array_with_capacity(v_size_329_);
lean_dec(v_size_329_);
v___x_332_ = ((lean_object*)(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__9));
v___x_333_ = lean_unsigned_to_nat(0u);
v___x_334_ = lean_array_get_size(v_buckets_330_);
v___x_335_ = lean_nat_dec_lt(v___x_333_, v___x_334_);
if (v___x_335_ == 0)
{
lean_dec_ref(v_buckets_330_);
lean_dec_ref(v___f_320_);
v___y_323_ = v___x_331_;
goto v___jp_322_;
}
else
{
lean_object* v___f_336_; uint8_t v___x_337_; 
v___f_336_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonHashSet___redArg___lam__2), 4, 2);
lean_closure_set(v___f_336_, 0, v___x_332_);
lean_closure_set(v___f_336_, 1, v___f_320_);
v___x_337_ = lean_nat_dec_le(v___x_334_, v___x_334_);
if (v___x_337_ == 0)
{
if (v___x_335_ == 0)
{
lean_dec_ref(v___f_336_);
lean_dec_ref(v_buckets_330_);
v___y_323_ = v___x_331_;
goto v___jp_322_;
}
else
{
size_t v___x_338_; size_t v___x_339_; lean_object* v___x_340_; 
v___x_338_ = ((size_t)0ULL);
v___x_339_ = lean_usize_of_nat(v___x_334_);
v___x_340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_332_, v___f_336_, v_buckets_330_, v___x_338_, v___x_339_, v___x_331_);
v___y_323_ = v___x_340_;
goto v___jp_322_;
}
}
else
{
size_t v___x_341_; size_t v___x_342_; lean_object* v___x_343_; 
v___x_341_ = ((size_t)0ULL);
v___x_342_ = lean_usize_of_nat(v___x_334_);
v___x_343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_332_, v___f_336_, v_buckets_330_, v___x_341_, v___x_342_, v___x_331_);
v___y_323_ = v___x_343_;
goto v___jp_322_;
}
}
v___jp_322_:
{
lean_object* v___x_324_; size_t v_sz_325_; size_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_324_ = ((lean_object*)(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__9));
v_sz_325_ = lean_array_size(v___y_323_);
v___x_326_ = ((size_t)0ULL);
v___x_327_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_324_, v___f_319_, v_sz_325_, v___x_326_, v___y_323_);
v___x_328_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg(lean_object* v_inst_345_){
_start:
{
lean_object* v___f_346_; lean_object* v___f_347_; lean_object* v___f_348_; 
v___f_346_ = ((lean_object*)(l_Lean_Lsp_instToJsonHashSet___redArg___closed__0));
v___f_347_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_347_, 0, v_inst_345_);
v___f_348_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3), 3, 2);
lean_closure_set(v___f_348_, 0, v___f_347_);
lean_closure_set(v___f_348_, 1, v___f_346_);
return v___f_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet(lean_object* v_00_u03b1_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_inst_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_Lsp_instToJsonHashSet___redArg(v_inst_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___boxed(lean_object* v_00_u03b1_354_, lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_inst_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Lsp_instToJsonHashSet(v_00_u03b1_354_, v_inst_355_, v_inst_356_, v_inst_357_);
lean_dec_ref(v_inst_356_);
lean_dec_ref(v_inst_355_);
return v_res_358_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_363_ = lean_box(0);
v___x_364_ = lean_unsigned_to_nat(16u);
v___x_365_ = lean_mk_array(v___x_364_, v___x_363_);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_366_ = lean_obj_once(&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2, &l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2_once, _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2);
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v___x_366_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0(lean_object* v___x_372_, lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_x_376_){
_start:
{
if (lean_obj_tag(v_x_376_) == 4)
{
lean_object* v_elems_377_; size_t v_sz_378_; size_t v___x_379_; lean_object* v___x_380_; 
v_elems_377_ = lean_ctor_get(v_x_376_, 0);
lean_inc_ref(v_elems_377_);
lean_dec_ref(v_x_376_);
v_sz_378_ = lean_array_size(v_elems_377_);
v___x_379_ = ((size_t)0ULL);
v___x_380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_372_, v_inst_373_, v_sz_378_, v___x_379_, v_elems_377_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec_ref(v_inst_375_);
lean_dec_ref(v_inst_374_);
v_a_381_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_380_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_399_; 
v_a_389_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_399_ == 0)
{
v___x_391_ = v___x_380_;
v_isShared_392_ = v_isSharedCheck_399_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_380_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_399_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___f_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_397_; 
v___f_393_ = ((lean_object*)(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__1));
v___x_394_ = lean_obj_once(&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3, &l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3_once, _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3);
v___x_395_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_393_, v_inst_374_, v_inst_375_, v___x_394_, v_a_389_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v___x_395_);
v___x_397_ = v___x_391_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
else
{
lean_object* v___x_400_; 
lean_dec(v_x_376_);
lean_dec_ref(v_inst_375_);
lean_dec_ref(v_inst_374_);
lean_dec_ref(v_inst_373_);
lean_dec_ref(v___x_372_);
v___x_400_ = ((lean_object*)(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__5));
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg(lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_inst_422_){
_start:
{
lean_object* v___x_423_; lean_object* v___f_424_; 
v___x_423_ = ((lean_object*)(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__9));
v___f_424_ = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0), 5, 4);
lean_closure_set(v___f_424_, 0, v___x_423_);
lean_closure_set(v___f_424_, 1, v_inst_422_);
lean_closure_set(v___f_424_, 2, v_inst_420_);
lean_closure_set(v___f_424_, 3, v_inst_421_);
return v___f_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHashSet(lean_object* v_00_u03b1_425_, lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_inst_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_Lsp_instFromJsonHashSet___redArg(v_inst_426_, v_inst_427_, v_inst_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0_spec__0(lean_object* v_x_430_){
_start:
{
if (lean_obj_tag(v_x_430_) == 0)
{
lean_object* v___x_431_; 
v___x_431_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1___closed__0));
return v___x_431_;
}
else
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_Json_getStr_x3f(v_x_430_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_432_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_432_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_449_; 
v_a_441_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_449_ == 0)
{
v___x_443_ = v___x_432_;
v_isShared_444_ = v_isSharedCheck_449_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_432_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_449_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_445_, 0, v_a_441_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_445_);
v___x_447_ = v___x_443_;
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
return v___x_447_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0(lean_object* v_j_450_, lean_object* v_k_451_){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = l_Lean_Json_getObjValD(v_j_450_, v_k_451_);
v___x_453_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0_spec__0(v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0___boxed(lean_object* v_j_454_, lean_object* v_k_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0(v_j_454_, v_k_455_);
lean_dec_ref(v_k_455_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3(size_t v_sz_457_, size_t v_i_458_, lean_object* v_bs_459_){
_start:
{
uint8_t v___x_460_; 
v___x_460_ = lean_usize_dec_lt(v_i_458_, v_sz_457_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; 
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v_bs_459_);
return v___x_461_;
}
else
{
lean_object* v_v_462_; lean_object* v___x_463_; 
v_v_462_ = lean_array_uget_borrowed(v_bs_459_, v_i_458_);
lean_inc(v_v_462_);
v___x_463_ = l_Lean_Json_getStr_x3f(v_v_462_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec_ref(v_bs_459_);
v_a_464_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_463_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_463_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_473_; lean_object* v_bs_x27_474_; size_t v___x_475_; size_t v___x_476_; lean_object* v___x_477_; 
v_a_472_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_a_472_);
lean_dec_ref(v___x_463_);
v___x_473_ = lean_unsigned_to_nat(0u);
v_bs_x27_474_ = lean_array_uset(v_bs_459_, v_i_458_, v___x_473_);
v___x_475_ = ((size_t)1ULL);
v___x_476_ = lean_usize_add(v_i_458_, v___x_475_);
v___x_477_ = lean_array_uset(v_bs_x27_474_, v_i_458_, v_a_472_);
v_i_458_ = v___x_476_;
v_bs_459_ = v___x_477_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3___boxed(lean_object* v_sz_479_, lean_object* v_i_480_, lean_object* v_bs_481_){
_start:
{
size_t v_sz_boxed_482_; size_t v_i_boxed_483_; lean_object* v_res_484_; 
v_sz_boxed_482_ = lean_unbox_usize(v_sz_479_);
lean_dec(v_sz_479_);
v_i_boxed_483_ = lean_unbox_usize(v_i_480_);
lean_dec(v_i_480_);
v_res_484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3(v_sz_boxed_482_, v_i_boxed_483_, v_bs_481_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10___redArg(lean_object* v_x_485_, lean_object* v_x_486_){
_start:
{
if (lean_obj_tag(v_x_486_) == 0)
{
return v_x_485_;
}
else
{
lean_object* v_key_487_; lean_object* v_value_488_; lean_object* v_tail_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_512_; 
v_key_487_ = lean_ctor_get(v_x_486_, 0);
v_value_488_ = lean_ctor_get(v_x_486_, 1);
v_tail_489_ = lean_ctor_get(v_x_486_, 2);
v_isSharedCheck_512_ = !lean_is_exclusive(v_x_486_);
if (v_isSharedCheck_512_ == 0)
{
v___x_491_ = v_x_486_;
v_isShared_492_ = v_isSharedCheck_512_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_tail_489_);
lean_inc(v_value_488_);
lean_inc(v_key_487_);
lean_dec(v_x_486_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_512_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_493_; uint64_t v___x_494_; uint64_t v___x_495_; uint64_t v___x_496_; uint64_t v_fold_497_; uint64_t v___x_498_; uint64_t v___x_499_; uint64_t v___x_500_; size_t v___x_501_; size_t v___x_502_; size_t v___x_503_; size_t v___x_504_; size_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_493_ = lean_array_get_size(v_x_485_);
v___x_494_ = lean_string_hash(v_key_487_);
v___x_495_ = 32ULL;
v___x_496_ = lean_uint64_shift_right(v___x_494_, v___x_495_);
v_fold_497_ = lean_uint64_xor(v___x_494_, v___x_496_);
v___x_498_ = 16ULL;
v___x_499_ = lean_uint64_shift_right(v_fold_497_, v___x_498_);
v___x_500_ = lean_uint64_xor(v_fold_497_, v___x_499_);
v___x_501_ = lean_uint64_to_usize(v___x_500_);
v___x_502_ = lean_usize_of_nat(v___x_493_);
v___x_503_ = ((size_t)1ULL);
v___x_504_ = lean_usize_sub(v___x_502_, v___x_503_);
v___x_505_ = lean_usize_land(v___x_501_, v___x_504_);
v___x_506_ = lean_array_uget_borrowed(v_x_485_, v___x_505_);
lean_inc(v___x_506_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 2, v___x_506_);
v___x_508_ = v___x_491_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_key_487_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_value_488_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v___x_506_);
v___x_508_ = v_reuseFailAlloc_511_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; 
v___x_509_ = lean_array_uset(v_x_485_, v___x_505_, v___x_508_);
v_x_485_ = v___x_509_;
v_x_486_ = v_tail_489_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8___redArg(lean_object* v_i_513_, lean_object* v_source_514_, lean_object* v_target_515_){
_start:
{
lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_516_ = lean_array_get_size(v_source_514_);
v___x_517_ = lean_nat_dec_lt(v_i_513_, v___x_516_);
if (v___x_517_ == 0)
{
lean_dec_ref(v_source_514_);
lean_dec(v_i_513_);
return v_target_515_;
}
else
{
lean_object* v_es_518_; lean_object* v___x_519_; lean_object* v_source_520_; lean_object* v_target_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v_es_518_ = lean_array_fget(v_source_514_, v_i_513_);
v___x_519_ = lean_box(0);
v_source_520_ = lean_array_fset(v_source_514_, v_i_513_, v___x_519_);
v_target_521_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10___redArg(v_target_515_, v_es_518_);
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_add(v_i_513_, v___x_522_);
lean_dec(v_i_513_);
v_i_513_ = v___x_523_;
v_source_514_ = v_source_520_;
v_target_515_ = v_target_521_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_data_525_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v_nbuckets_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_526_ = lean_array_get_size(v_data_525_);
v___x_527_ = lean_unsigned_to_nat(2u);
v_nbuckets_528_ = lean_nat_mul(v___x_526_, v___x_527_);
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = lean_box(0);
v___x_531_ = lean_mk_array(v_nbuckets_528_, v___x_530_);
v___x_532_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8___redArg(v___x_529_, v_data_525_, v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_a_533_, lean_object* v_x_534_){
_start:
{
if (lean_obj_tag(v_x_534_) == 0)
{
uint8_t v___x_535_; 
v___x_535_ = 0;
return v___x_535_;
}
else
{
lean_object* v_key_536_; lean_object* v_tail_537_; uint8_t v___x_538_; 
v_key_536_ = lean_ctor_get(v_x_534_, 0);
v_tail_537_ = lean_ctor_get(v_x_534_, 2);
v___x_538_ = lean_string_dec_eq(v_key_536_, v_a_533_);
if (v___x_538_ == 0)
{
v_x_534_ = v_tail_537_;
goto _start;
}
else
{
return v___x_538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_a_540_, lean_object* v_x_541_){
_start:
{
uint8_t v_res_542_; lean_object* v_r_543_; 
v_res_542_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_a_540_, v_x_541_);
lean_dec(v_x_541_);
lean_dec_ref(v_a_540_);
v_r_543_ = lean_box(v_res_542_);
return v_r_543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_m_544_, lean_object* v_a_545_, lean_object* v_b_546_){
_start:
{
lean_object* v_size_547_; lean_object* v_buckets_548_; lean_object* v___x_549_; uint64_t v___x_550_; uint64_t v___x_551_; uint64_t v___x_552_; uint64_t v_fold_553_; uint64_t v___x_554_; uint64_t v___x_555_; uint64_t v___x_556_; size_t v___x_557_; size_t v___x_558_; size_t v___x_559_; size_t v___x_560_; size_t v___x_561_; lean_object* v_bkt_562_; uint8_t v___x_563_; 
v_size_547_ = lean_ctor_get(v_m_544_, 0);
v_buckets_548_ = lean_ctor_get(v_m_544_, 1);
v___x_549_ = lean_array_get_size(v_buckets_548_);
v___x_550_ = lean_string_hash(v_a_545_);
v___x_551_ = 32ULL;
v___x_552_ = lean_uint64_shift_right(v___x_550_, v___x_551_);
v_fold_553_ = lean_uint64_xor(v___x_550_, v___x_552_);
v___x_554_ = 16ULL;
v___x_555_ = lean_uint64_shift_right(v_fold_553_, v___x_554_);
v___x_556_ = lean_uint64_xor(v_fold_553_, v___x_555_);
v___x_557_ = lean_uint64_to_usize(v___x_556_);
v___x_558_ = lean_usize_of_nat(v___x_549_);
v___x_559_ = ((size_t)1ULL);
v___x_560_ = lean_usize_sub(v___x_558_, v___x_559_);
v___x_561_ = lean_usize_land(v___x_557_, v___x_560_);
v_bkt_562_ = lean_array_uget_borrowed(v_buckets_548_, v___x_561_);
v___x_563_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_a_545_, v_bkt_562_);
if (v___x_563_ == 0)
{
lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_584_; 
lean_inc_ref(v_buckets_548_);
lean_inc(v_size_547_);
v_isSharedCheck_584_ = !lean_is_exclusive(v_m_544_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; lean_object* v_unused_586_; 
v_unused_585_ = lean_ctor_get(v_m_544_, 1);
lean_dec(v_unused_585_);
v_unused_586_ = lean_ctor_get(v_m_544_, 0);
lean_dec(v_unused_586_);
v___x_565_ = v_m_544_;
v_isShared_566_ = v_isSharedCheck_584_;
goto v_resetjp_564_;
}
else
{
lean_dec(v_m_544_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_584_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v_size_x27_568_; lean_object* v___x_569_; lean_object* v_buckets_x27_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_567_ = lean_unsigned_to_nat(1u);
v_size_x27_568_ = lean_nat_add(v_size_547_, v___x_567_);
lean_dec(v_size_547_);
lean_inc(v_bkt_562_);
v___x_569_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_569_, 0, v_a_545_);
lean_ctor_set(v___x_569_, 1, v_b_546_);
lean_ctor_set(v___x_569_, 2, v_bkt_562_);
v_buckets_x27_570_ = lean_array_uset(v_buckets_548_, v___x_561_, v___x_569_);
v___x_571_ = lean_unsigned_to_nat(4u);
v___x_572_ = lean_nat_mul(v_size_x27_568_, v___x_571_);
v___x_573_ = lean_unsigned_to_nat(3u);
v___x_574_ = lean_nat_div(v___x_572_, v___x_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_array_get_size(v_buckets_x27_570_);
v___x_576_ = lean_nat_dec_le(v___x_574_, v___x_575_);
lean_dec(v___x_574_);
if (v___x_576_ == 0)
{
lean_object* v_val_577_; lean_object* v___x_579_; 
v_val_577_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7___redArg(v_buckets_x27_570_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v_val_577_);
lean_ctor_set(v___x_565_, 0, v_size_x27_568_);
v___x_579_ = v___x_565_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_size_x27_568_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v_val_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
else
{
lean_object* v___x_582_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v_buckets_x27_570_);
lean_ctor_set(v___x_565_, 0, v_size_x27_568_);
v___x_582_ = v___x_565_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_size_x27_568_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_buckets_x27_570_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
else
{
lean_dec(v_b_546_);
lean_dec_ref(v_a_545_);
return v_m_544_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6(lean_object* v_as_587_, size_t v_sz_588_, size_t v_i_589_, lean_object* v_b_590_){
_start:
{
uint8_t v___x_591_; 
v___x_591_ = lean_usize_dec_lt(v_i_589_, v_sz_588_);
if (v___x_591_ == 0)
{
return v_b_590_;
}
else
{
lean_object* v_a_592_; lean_object* v___x_593_; lean_object* v_r_594_; size_t v___x_595_; size_t v___x_596_; 
v_a_592_ = lean_array_uget_borrowed(v_as_587_, v_i_589_);
v___x_593_ = lean_box(0);
lean_inc(v_a_592_);
v_r_594_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(v_b_590_, v_a_592_, v___x_593_);
v___x_595_ = ((size_t)1ULL);
v___x_596_ = lean_usize_add(v_i_589_, v___x_595_);
v_i_589_ = v___x_596_;
v_b_590_ = v_r_594_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_as_598_, lean_object* v_sz_599_, lean_object* v_i_600_, lean_object* v_b_601_){
_start:
{
size_t v_sz_boxed_602_; size_t v_i_boxed_603_; lean_object* v_res_604_; 
v_sz_boxed_602_ = lean_unbox_usize(v_sz_599_);
lean_dec(v_sz_599_);
v_i_boxed_603_ = lean_unbox_usize(v_i_600_);
lean_dec(v_i_600_);
v_res_604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6(v_as_598_, v_sz_boxed_602_, v_i_boxed_603_, v_b_601_);
lean_dec_ref(v_as_598_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4(lean_object* v_m_605_, lean_object* v_l_606_){
_start:
{
size_t v_sz_607_; size_t v___x_608_; lean_object* v___x_609_; 
v_sz_607_ = lean_array_size(v_l_606_);
v___x_608_ = ((size_t)0ULL);
v___x_609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6(v_l_606_, v_sz_607_, v___x_608_, v_m_605_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4___boxed(lean_object* v_m_610_, lean_object* v_l_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4(v_m_610_, v_l_611_);
lean_dec_ref(v_l_611_);
return v_res_612_;
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_615_ = lean_box(0);
v___x_616_ = lean_unsigned_to_nat(16u);
v___x_617_ = lean_mk_array(v___x_616_, v___x_615_);
return v___x_617_;
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_618_ = lean_obj_once(&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1, &l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1_once, _init_l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1);
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v___x_618_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2(lean_object* v_x_623_){
_start:
{
if (lean_obj_tag(v_x_623_) == 0)
{
lean_object* v___x_624_; 
v___x_624_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__0));
return v___x_624_;
}
else
{
if (lean_obj_tag(v_x_623_) == 4)
{
lean_object* v_elems_625_; size_t v_sz_626_; size_t v___x_627_; lean_object* v___x_628_; 
v_elems_625_ = lean_ctor_get(v_x_623_, 0);
lean_inc_ref(v_elems_625_);
lean_dec_ref(v_x_623_);
v_sz_626_ = lean_array_size(v_elems_625_);
v___x_627_ = ((size_t)0ULL);
v___x_628_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3(v_sz_626_, v___x_627_, v_elems_625_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_628_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_628_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_647_; 
v_a_637_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_647_ == 0)
{
v___x_639_ = v___x_628_;
v_isShared_640_ = v_isSharedCheck_647_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_628_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_647_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_641_ = lean_obj_once(&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2, &l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2_once, _init_l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2);
v___x_642_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4(v___x_641_, v_a_637_);
lean_dec(v_a_637_);
v___x_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_643_);
v___x_645_ = v___x_639_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
else
{
lean_object* v___x_648_; 
lean_dec(v_x_623_);
v___x_648_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__3));
return v___x_648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(lean_object* v_j_649_, lean_object* v_k_650_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = l_Lean_Json_getObjValD(v_j_649_, v_k_650_);
v___x_652_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2(v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1___boxed(lean_object* v_j_653_, lean_object* v_k_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(v_j_653_, v_k_654_);
lean_dec_ref(v_k_654_);
return v_res_655_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3(void){
_start:
{
uint8_t v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_662_ = 1;
v___x_663_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2));
v___x_664_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_663_, v___x_662_);
return v___x_664_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5));
v___x_666_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3);
v___x_667_ = lean_string_append(v___x_666_, v___x_665_);
return v___x_667_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7(void){
_start:
{
uint8_t v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_671_ = 1;
v___x_672_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__6));
v___x_673_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_672_, v___x_671_);
return v___x_673_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7);
v___x_675_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4);
v___x_676_ = lean_string_append(v___x_675_, v___x_674_);
return v___x_676_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_677_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_678_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8);
v___x_679_ = lean_string_append(v___x_678_, v___x_677_);
return v___x_679_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13(void){
_start:
{
uint8_t v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_684_ = 1;
v___x_685_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__12));
v___x_686_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_685_, v___x_684_);
return v___x_686_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13);
v___x_688_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4);
v___x_689_ = lean_string_append(v___x_688_, v___x_687_);
return v___x_689_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_690_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_691_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14);
v___x_692_ = lean_string_append(v___x_691_, v___x_690_);
return v___x_692_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19(void){
_start:
{
uint8_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_697_ = 1;
v___x_698_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__18));
v___x_699_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_698_, v___x_697_);
return v___x_699_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19);
v___x_701_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4);
v___x_702_ = lean_string_append(v___x_701_, v___x_700_);
return v___x_702_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_703_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_704_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20);
v___x_705_ = lean_string_append(v___x_704_, v___x_703_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson(lean_object* v_json_706_){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__0));
lean_inc(v_json_706_);
v___x_708_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0(v_json_706_, v___x_707_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_718_; 
lean_dec(v_json_706_);
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_718_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_718_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_718_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_713_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9);
v___x_714_ = lean_string_append(v___x_713_, v_a_709_);
lean_dec(v_a_709_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_714_);
v___x_716_ = v___x_711_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
else
{
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec(v_json_706_);
v_a_719_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_708_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_708_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set_tag(v___x_721_, 0);
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_a_727_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_727_);
lean_dec_ref(v___x_708_);
v___x_728_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__10));
lean_inc(v_json_706_);
v___x_729_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(v_json_706_, v___x_728_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_739_; 
lean_dec(v_a_727_);
lean_dec(v_json_706_);
v_a_730_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_739_ == 0)
{
v___x_732_ = v___x_729_;
v_isShared_733_ = v_isSharedCheck_739_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_729_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_739_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_734_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15);
v___x_735_ = lean_string_append(v___x_734_, v_a_730_);
lean_dec(v_a_730_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v___x_735_);
v___x_737_ = v___x_732_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
else
{
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec(v_a_727_);
lean_dec(v_json_706_);
v_a_740_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_729_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_729_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set_tag(v___x_742_, 0);
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v_a_748_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_748_);
lean_dec_ref(v___x_729_);
v___x_749_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__16));
v___x_750_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(v_json_706_, v___x_749_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_760_; 
lean_dec(v_a_748_);
lean_dec(v_a_727_);
v_a_751_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_760_ == 0)
{
v___x_753_ = v___x_750_;
v_isShared_754_ = v_isSharedCheck_760_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_750_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_760_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
v___x_755_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21);
v___x_756_ = lean_string_append(v___x_755_, v_a_751_);
lean_dec(v_a_751_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v___x_756_);
v___x_758_ = v___x_753_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
else
{
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec(v_a_748_);
lean_dec(v_a_727_);
v_a_761_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_750_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_750_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set_tag(v___x_763_, 0);
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_777_; 
v_a_769_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_777_ == 0)
{
v___x_771_ = v___x_750_;
v_isShared_772_ = v_isSharedCheck_777_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_750_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_777_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_773_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_773_, 0, v_a_727_);
lean_ctor_set(v___x_773_, 1, v_a_748_);
lean_ctor_set(v___x_773_, 2, v_a_769_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_773_);
v___x_775_ = v___x_771_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_778_, lean_object* v_m_779_, lean_object* v_a_780_, lean_object* v_b_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(v_m_779_, v_a_780_, v_b_781_);
return v___x_782_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_783_, lean_object* v_a_784_, lean_object* v_x_785_){
_start:
{
uint8_t v___x_786_; 
v___x_786_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_a_784_, v_x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_00_u03b2_787_, lean_object* v_a_788_, lean_object* v_x_789_){
_start:
{
uint8_t v_res_790_; lean_object* v_r_791_; 
v_res_790_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6(v_00_u03b2_787_, v_a_788_, v_x_789_);
lean_dec(v_x_789_);
lean_dec_ref(v_a_788_);
v_r_791_ = lean_box(v_res_790_);
return v_r_791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_792_, lean_object* v_data_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7___redArg(v_data_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8(lean_object* v_00_u03b2_795_, lean_object* v_i_796_, lean_object* v_source_797_, lean_object* v_target_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8___redArg(v_i_796_, v_source_797_, v_target_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10(lean_object* v_00_u03b2_800_, lean_object* v_x_801_, lean_object* v_x_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10___redArg(v_x_801_, v_x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__0(lean_object* v_k_806_, lean_object* v_x_807_){
_start:
{
if (lean_obj_tag(v_x_807_) == 0)
{
lean_object* v___x_808_; 
lean_dec_ref(v_k_806_);
v___x_808_ = lean_box(0);
return v___x_808_;
}
else
{
lean_object* v_val_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_819_; 
v_val_809_ = lean_ctor_get(v_x_807_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v_x_807_);
if (v_isSharedCheck_819_ == 0)
{
v___x_811_ = v_x_807_;
v_isShared_812_ = v_isSharedCheck_819_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_val_809_);
lean_dec(v_x_807_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_819_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
lean_ctor_set_tag(v___x_811_, 3);
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_val_809_);
v___x_814_ = v_reuseFailAlloc_818_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v_k_806_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = lean_box(0);
v___x_817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
return v___x_817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1(size_t v_sz_820_, size_t v_i_821_, lean_object* v_bs_822_){
_start:
{
uint8_t v___x_823_; 
v___x_823_ = lean_usize_dec_lt(v_i_821_, v_sz_820_);
if (v___x_823_ == 0)
{
return v_bs_822_;
}
else
{
lean_object* v_v_824_; lean_object* v___x_825_; lean_object* v_bs_x27_826_; lean_object* v___x_827_; size_t v___x_828_; size_t v___x_829_; lean_object* v___x_830_; 
v_v_824_ = lean_array_uget(v_bs_822_, v_i_821_);
v___x_825_ = lean_unsigned_to_nat(0u);
v_bs_x27_826_ = lean_array_uset(v_bs_822_, v_i_821_, v___x_825_);
v___x_827_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_827_, 0, v_v_824_);
v___x_828_ = ((size_t)1ULL);
v___x_829_ = lean_usize_add(v_i_821_, v___x_828_);
v___x_830_ = lean_array_uset(v_bs_x27_826_, v_i_821_, v___x_827_);
v_i_821_ = v___x_829_;
v_bs_822_ = v___x_830_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1___boxed(lean_object* v_sz_832_, lean_object* v_i_833_, lean_object* v_bs_834_){
_start:
{
size_t v_sz_boxed_835_; size_t v_i_boxed_836_; lean_object* v_res_837_; 
v_sz_boxed_835_ = lean_unbox_usize(v_sz_832_);
lean_dec(v_sz_832_);
v_i_boxed_836_ = lean_unbox_usize(v_i_833_);
lean_dec(v_i_833_);
v_res_837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1(v_sz_boxed_835_, v_i_boxed_836_, v_bs_834_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__2(lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
if (lean_obj_tag(v_x_839_) == 0)
{
return v_x_838_;
}
else
{
lean_object* v_key_840_; lean_object* v_tail_841_; lean_object* v___x_842_; 
v_key_840_ = lean_ctor_get(v_x_839_, 0);
lean_inc(v_key_840_);
v_tail_841_ = lean_ctor_get(v_x_839_, 2);
lean_inc(v_tail_841_);
lean_dec_ref(v_x_839_);
v___x_842_ = lean_array_push(v_x_838_, v_key_840_);
v_x_838_ = v___x_842_;
v_x_839_ = v_tail_841_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__3(lean_object* v_as_844_, size_t v_i_845_, size_t v_stop_846_, lean_object* v_b_847_){
_start:
{
uint8_t v___x_848_; 
v___x_848_ = lean_usize_dec_eq(v_i_845_, v_stop_846_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; size_t v___x_851_; size_t v___x_852_; 
v___x_849_ = lean_array_uget_borrowed(v_as_844_, v_i_845_);
lean_inc(v___x_849_);
v___x_850_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__2(v_b_847_, v___x_849_);
v___x_851_ = ((size_t)1ULL);
v___x_852_ = lean_usize_add(v_i_845_, v___x_851_);
v_i_845_ = v___x_852_;
v_b_847_ = v___x_850_;
goto _start;
}
else
{
return v_b_847_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__3___boxed(lean_object* v_as_854_, lean_object* v_i_855_, lean_object* v_stop_856_, lean_object* v_b_857_){
_start:
{
size_t v_i_boxed_858_; size_t v_stop_boxed_859_; lean_object* v_res_860_; 
v_i_boxed_858_ = lean_unbox_usize(v_i_855_);
lean_dec(v_i_855_);
v_stop_boxed_859_ = lean_unbox_usize(v_stop_856_);
lean_dec(v_stop_856_);
v_res_860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__3(v_as_854_, v_i_boxed_858_, v_stop_boxed_859_, v_b_857_);
lean_dec_ref(v_as_854_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(lean_object* v_k_861_, lean_object* v_x_862_){
_start:
{
lean_object* v___y_864_; 
if (lean_obj_tag(v_x_862_) == 0)
{
lean_object* v___x_872_; 
lean_dec_ref(v_k_861_);
v___x_872_ = lean_box(0);
return v___x_872_;
}
else
{
lean_object* v_val_873_; lean_object* v_size_874_; lean_object* v_buckets_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v_val_873_ = lean_ctor_get(v_x_862_, 0);
v_size_874_ = lean_ctor_get(v_val_873_, 0);
v_buckets_875_ = lean_ctor_get(v_val_873_, 1);
v___x_876_ = lean_mk_empty_array_with_capacity(v_size_874_);
v___x_877_ = lean_unsigned_to_nat(0u);
v___x_878_ = lean_array_get_size(v_buckets_875_);
v___x_879_ = lean_nat_dec_lt(v___x_877_, v___x_878_);
if (v___x_879_ == 0)
{
v___y_864_ = v___x_876_;
goto v___jp_863_;
}
else
{
uint8_t v___x_880_; 
v___x_880_ = lean_nat_dec_le(v___x_878_, v___x_878_);
if (v___x_880_ == 0)
{
if (v___x_879_ == 0)
{
v___y_864_ = v___x_876_;
goto v___jp_863_;
}
else
{
size_t v___x_881_; size_t v___x_882_; lean_object* v___x_883_; 
v___x_881_ = ((size_t)0ULL);
v___x_882_ = lean_usize_of_nat(v___x_878_);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__3(v_buckets_875_, v___x_881_, v___x_882_, v___x_876_);
v___y_864_ = v___x_883_;
goto v___jp_863_;
}
}
else
{
size_t v___x_884_; size_t v___x_885_; lean_object* v___x_886_; 
v___x_884_ = ((size_t)0ULL);
v___x_885_ = lean_usize_of_nat(v___x_878_);
v___x_886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__3(v_buckets_875_, v___x_884_, v___x_885_, v___x_876_);
v___y_864_ = v___x_886_;
goto v___jp_863_;
}
}
}
v___jp_863_:
{
size_t v_sz_865_; size_t v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_sz_865_ = lean_array_size(v___y_864_);
v___x_866_ = ((size_t)0ULL);
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1(v_sz_865_, v___x_866_, v___y_864_);
v___x_868_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v_k_861_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = lean_box(0);
v___x_871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_869_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
return v___x_871_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1___boxed(lean_object* v_k_887_, lean_object* v_x_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(v_k_887_, v_x_888_);
lean_dec(v_x_888_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLogConfig_toJson(lean_object* v_x_890_){
_start:
{
lean_object* v_logDir_x3f_891_; lean_object* v_allowedMethods_x3f_892_; lean_object* v_disallowedMethods_x3f_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_logDir_x3f_891_ = lean_ctor_get(v_x_890_, 0);
lean_inc(v_logDir_x3f_891_);
v_allowedMethods_x3f_892_ = lean_ctor_get(v_x_890_, 1);
lean_inc(v_allowedMethods_x3f_892_);
v_disallowedMethods_x3f_893_ = lean_ctor_get(v_x_890_, 2);
lean_inc(v_disallowedMethods_x3f_893_);
lean_dec_ref(v_x_890_);
v___x_894_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__0));
v___x_895_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__0(v___x_894_, v_logDir_x3f_891_);
v___x_896_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__10));
v___x_897_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(v___x_896_, v_allowedMethods_x3f_892_);
lean_dec(v_allowedMethods_x3f_892_);
v___x_898_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__16));
v___x_899_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(v___x_898_, v_disallowedMethods_x3f_893_);
lean_dec(v_disallowedMethods_x3f_893_);
v___x_900_ = lean_box(0);
v___x_901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_897_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_895_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2));
v___x_905_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_903_, v___x_904_);
v___x_906_ = l_Lean_Json_mkObj(v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0(lean_object* v_k_909_, lean_object* v_x_910_){
_start:
{
if (lean_obj_tag(v_x_910_) == 0)
{
lean_object* v___x_911_; 
lean_dec_ref(v_k_909_);
v___x_911_ = lean_box(0);
return v___x_911_;
}
else
{
lean_object* v_val_912_; lean_object* v___x_913_; uint8_t v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_val_912_ = lean_ctor_get(v_x_910_, 0);
v___x_913_ = lean_alloc_ctor(1, 0, 1);
v___x_914_ = lean_unbox(v_val_912_);
lean_ctor_set_uint8(v___x_913_, 0, v___x_914_);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v_k_909_);
lean_ctor_set(v___x_915_, 1, v___x_913_);
v___x_916_ = lean_box(0);
v___x_917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_915_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
return v___x_917_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0___boxed(lean_object* v_k_918_, lean_object* v_x_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0(v_k_918_, v_x_919_);
lean_dec(v_x_919_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__1(lean_object* v_k_921_, lean_object* v_x_922_){
_start:
{
if (lean_obj_tag(v_x_922_) == 0)
{
lean_object* v___x_923_; 
lean_dec_ref(v_k_921_);
v___x_923_ = lean_box(0);
return v___x_923_;
}
else
{
lean_object* v_val_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_val_924_ = lean_ctor_get(v_x_922_, 0);
lean_inc(v_val_924_);
lean_dec_ref(v_x_922_);
v___x_925_ = l_Lean_Lsp_instToJsonLogConfig_toJson(v_val_924_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_k_921_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = lean_box(0);
v___x_928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_926_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
return v___x_928_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonInitializationOptions_toJson(lean_object* v_x_931_){
_start:
{
lean_object* v_hasWidgets_x3f_932_; lean_object* v_logCfg_x3f_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_949_; 
v_hasWidgets_x3f_932_ = lean_ctor_get(v_x_931_, 0);
v_logCfg_x3f_933_ = lean_ctor_get(v_x_931_, 1);
v_isSharedCheck_949_ = !lean_is_exclusive(v_x_931_);
if (v_isSharedCheck_949_ == 0)
{
v___x_935_ = v_x_931_;
v_isShared_936_ = v_isSharedCheck_949_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_logCfg_x3f_933_);
lean_inc(v_hasWidgets_x3f_932_);
lean_dec(v_x_931_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_949_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_937_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__0));
v___x_938_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0(v___x_937_, v_hasWidgets_x3f_932_);
lean_dec(v_hasWidgets_x3f_932_);
v___x_939_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__1));
v___x_940_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__1(v___x_939_, v_logCfg_x3f_933_);
v___x_941_ = lean_box(0);
if (v_isShared_936_ == 0)
{
lean_ctor_set_tag(v___x_935_, 1);
lean_ctor_set(v___x_935_, 1, v___x_941_);
lean_ctor_set(v___x_935_, 0, v___x_940_);
v___x_943_ = v___x_935_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v___x_941_);
v___x_943_ = v_reuseFailAlloc_948_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_938_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2));
v___x_946_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_944_, v___x_945_);
v___x_947_ = l_Lean_Json_mkObj(v___x_946_);
return v___x_947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2(lean_object* v_x_954_){
_start:
{
if (lean_obj_tag(v_x_954_) == 0)
{
lean_object* v___x_955_; 
v___x_955_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2___closed__0));
return v___x_955_;
}
else
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_Lsp_instFromJsonLogConfig_fromJson(v_x_954_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_973_; 
v_a_965_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_973_ == 0)
{
v___x_967_ = v___x_956_;
v_isShared_968_ = v_isSharedCheck_973_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_956_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_973_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_969_, 0, v_a_965_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v___x_969_);
v___x_971_ = v___x_967_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1(lean_object* v_j_974_, lean_object* v_k_975_){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = l_Lean_Json_getObjValD(v_j_974_, v_k_975_);
v___x_977_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2(v___x_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1___boxed(lean_object* v_j_978_, lean_object* v_k_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1(v_j_978_, v_k_979_);
lean_dec_ref(v_k_979_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0(lean_object* v_x_983_){
_start:
{
if (lean_obj_tag(v_x_983_) == 0)
{
lean_object* v___x_984_; 
v___x_984_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___closed__0));
return v___x_984_;
}
else
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_Json_getBool_x3f(v_x_983_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1002_; 
v_a_994_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_996_ = v___x_985_;
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_985_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_998_, 0, v_a_994_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_998_);
v___x_1000_ = v___x_996_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___boxed(lean_object* v_x_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0(v_x_1003_);
lean_dec(v_x_1003_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0(lean_object* v_j_1005_, lean_object* v_k_1006_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = l_Lean_Json_getObjValD(v_j_1005_, v_k_1006_);
v___x_1008_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0(v___x_1007_);
lean_dec(v___x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0___boxed(lean_object* v_j_1009_, lean_object* v_k_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0(v_j_1009_, v_k_1010_);
lean_dec_ref(v_k_1010_);
return v_res_1011_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1017_ = 1;
v___x_1018_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1));
v___x_1019_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1018_, v___x_1017_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1020_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5));
v___x_1021_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2);
v___x_1022_ = lean_string_append(v___x_1021_, v___x_1020_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = 1;
v___x_1027_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__5));
v___x_1028_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1027_, v___x_1026_);
return v___x_1028_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6);
v___x_1030_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3);
v___x_1031_ = lean_string_append(v___x_1030_, v___x_1029_);
return v___x_1031_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1032_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_1033_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7);
v___x_1034_ = lean_string_append(v___x_1033_, v___x_1032_);
return v___x_1034_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11(void){
_start:
{
uint8_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1038_ = 1;
v___x_1039_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__10));
v___x_1040_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1039_, v___x_1038_);
return v___x_1040_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1041_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11);
v___x_1042_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3);
v___x_1043_ = lean_string_append(v___x_1042_, v___x_1041_);
return v___x_1043_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1044_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_1045_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12);
v___x_1046_ = lean_string_append(v___x_1045_, v___x_1044_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializationOptions_fromJson(lean_object* v_json_1047_){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__0));
lean_inc(v_json_1047_);
v___x_1049_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0(v_json_1047_, v___x_1048_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1059_; 
lean_dec(v_json_1047_);
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1052_ = v___x_1049_;
v_isShared_1053_ = v_isSharedCheck_1059_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1049_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1059_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1054_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8);
v___x_1055_ = lean_string_append(v___x_1054_, v_a_1050_);
lean_dec(v_a_1050_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v___x_1055_);
v___x_1057_ = v___x_1052_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
else
{
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_dec(v_json_1047_);
v_a_1060_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1049_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1049_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set_tag(v___x_1062_, 0);
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
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
lean_object* v_a_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_a_1068_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_a_1068_);
lean_dec_ref(v___x_1049_);
v___x_1069_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__1));
v___x_1070_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1(v_json_1047_, v___x_1069_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1080_; 
lean_dec(v_a_1068_);
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1080_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1080_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1075_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13);
v___x_1076_ = lean_string_append(v___x_1075_, v_a_1071_);
lean_dec(v_a_1071_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v___x_1076_);
v___x_1078_ = v___x_1073_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
else
{
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec(v_a_1068_);
v_a_1081_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1070_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1070_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
lean_ctor_set_tag(v___x_1083_, 0);
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1097_; 
v_a_1089_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1091_ = v___x_1070_;
v_isShared_1092_ = v_isSharedCheck_1097_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1070_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1097_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
v___x_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1093_, 0, v_a_1068_);
lean_ctor_set(v___x_1093_, 1, v_a_1089_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v___x_1093_);
v___x_1095_ = v___x_1091_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__0(lean_object* v_k_1100_, lean_object* v_x_1101_){
_start:
{
if (lean_obj_tag(v_x_1101_) == 0)
{
lean_object* v___x_1102_; 
lean_dec_ref(v_k_1100_);
v___x_1102_ = lean_box(0);
return v___x_1102_;
}
else
{
lean_object* v_val_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1114_; 
v_val_1103_ = lean_ctor_get(v_x_1101_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_x_1101_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1105_ = v_x_1101_;
v_isShared_1106_ = v_isSharedCheck_1114_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_val_1103_);
lean_dec(v_x_1101_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1114_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1107_ = l_Lean_JsonNumber_fromInt(v_val_1103_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set_tag(v___x_1105_, 2);
lean_ctor_set(v___x_1105_, 0, v___x_1107_);
v___x_1109_ = v___x_1105_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1110_, 0, v_k_1100_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1110_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
return v___x_1112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__1(lean_object* v_k_1115_, lean_object* v_x_1116_){
_start:
{
if (lean_obj_tag(v_x_1116_) == 0)
{
lean_object* v___x_1117_; 
lean_dec_ref(v_k_1115_);
v___x_1117_ = lean_box(0);
return v___x_1117_;
}
else
{
lean_object* v_val_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v_val_1118_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_val_1118_);
lean_dec_ref(v_x_1116_);
v___x_1119_ = l_Lean_Lsp_instToJsonClientInfo_toJson(v_val_1118_);
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v_k_1115_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = lean_box(0);
v___x_1122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
return v___x_1122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__2(lean_object* v_k_1123_, lean_object* v_x_1124_){
_start:
{
if (lean_obj_tag(v_x_1124_) == 0)
{
lean_object* v___x_1125_; 
lean_dec_ref(v_k_1123_);
v___x_1125_ = lean_box(0);
return v___x_1125_;
}
else
{
lean_object* v_val_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v_val_1126_ = lean_ctor_get(v_x_1124_, 0);
lean_inc(v_val_1126_);
lean_dec_ref(v_x_1124_);
v___x_1127_ = l_Lean_Lsp_instToJsonInitializationOptions_toJson(v_val_1126_);
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v_k_1123_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = lean_box(0);
v___x_1130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1128_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
return v___x_1130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4(size_t v_sz_1131_, size_t v_i_1132_, lean_object* v_bs_1133_){
_start:
{
uint8_t v___x_1134_; 
v___x_1134_ = lean_usize_dec_lt(v_i_1132_, v_sz_1131_);
if (v___x_1134_ == 0)
{
return v_bs_1133_;
}
else
{
lean_object* v_v_1135_; lean_object* v___x_1136_; lean_object* v_bs_x27_1137_; lean_object* v___x_1138_; size_t v___x_1139_; size_t v___x_1140_; lean_object* v___x_1141_; 
v_v_1135_ = lean_array_uget(v_bs_1133_, v_i_1132_);
v___x_1136_ = lean_unsigned_to_nat(0u);
v_bs_x27_1137_ = lean_array_uset(v_bs_1133_, v_i_1132_, v___x_1136_);
v___x_1138_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson(v_v_1135_);
v___x_1139_ = ((size_t)1ULL);
v___x_1140_ = lean_usize_add(v_i_1132_, v___x_1139_);
v___x_1141_ = lean_array_uset(v_bs_x27_1137_, v_i_1132_, v___x_1138_);
v_i_1132_ = v___x_1140_;
v_bs_1133_ = v___x_1141_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_1143_, lean_object* v_i_1144_, lean_object* v_bs_1145_){
_start:
{
size_t v_sz_boxed_1146_; size_t v_i_boxed_1147_; lean_object* v_res_1148_; 
v_sz_boxed_1146_ = lean_unbox_usize(v_sz_1143_);
lean_dec(v_sz_1143_);
v_i_boxed_1147_ = lean_unbox_usize(v_i_1144_);
lean_dec(v_i_1144_);
v_res_1148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4(v_sz_boxed_1146_, v_i_boxed_1147_, v_bs_1145_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3(lean_object* v_a_1149_){
_start:
{
size_t v_sz_1150_; size_t v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v_sz_1150_ = lean_array_size(v_a_1149_);
v___x_1151_ = ((size_t)0ULL);
v___x_1152_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4(v_sz_1150_, v___x_1151_, v_a_1149_);
v___x_1153_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3(lean_object* v_k_1154_, lean_object* v_x_1155_){
_start:
{
if (lean_obj_tag(v_x_1155_) == 0)
{
lean_object* v___x_1156_; 
lean_dec_ref(v_k_1154_);
v___x_1156_ = lean_box(0);
return v___x_1156_;
}
else
{
lean_object* v_val_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v_val_1157_ = lean_ctor_get(v_x_1155_, 0);
lean_inc(v_val_1157_);
lean_dec_ref(v_x_1155_);
v___x_1158_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3(v_val_1157_);
v___x_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1159_, 0, v_k_1154_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = lean_box(0);
v___x_1161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1159_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
return v___x_1161_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonInitializeParams_toJson(lean_object* v_x_1169_){
_start:
{
lean_object* v_processId_x3f_1170_; lean_object* v_clientInfo_x3f_1171_; lean_object* v_rootUri_x3f_1172_; lean_object* v_initializationOptions_x3f_1173_; lean_object* v_capabilities_1174_; uint8_t v_trace_1175_; lean_object* v_workspaceFolders_x3f_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___y_1192_; 
v_processId_x3f_1170_ = lean_ctor_get(v_x_1169_, 0);
lean_inc(v_processId_x3f_1170_);
v_clientInfo_x3f_1171_ = lean_ctor_get(v_x_1169_, 1);
lean_inc(v_clientInfo_x3f_1171_);
v_rootUri_x3f_1172_ = lean_ctor_get(v_x_1169_, 2);
lean_inc(v_rootUri_x3f_1172_);
v_initializationOptions_x3f_1173_ = lean_ctor_get(v_x_1169_, 3);
lean_inc(v_initializationOptions_x3f_1173_);
v_capabilities_1174_ = lean_ctor_get(v_x_1169_, 4);
lean_inc_ref(v_capabilities_1174_);
v_trace_1175_ = lean_ctor_get_uint8(v_x_1169_, sizeof(void*)*6);
v_workspaceFolders_x3f_1176_ = lean_ctor_get(v_x_1169_, 5);
lean_inc(v_workspaceFolders_x3f_1176_);
lean_dec_ref(v_x_1169_);
v___x_1177_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__0));
v___x_1178_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__0(v___x_1177_, v_processId_x3f_1170_);
v___x_1179_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__1));
v___x_1180_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__1(v___x_1179_, v_clientInfo_x3f_1171_);
v___x_1181_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__2));
v___x_1182_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__0(v___x_1181_, v_rootUri_x3f_1172_);
v___x_1183_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__3));
v___x_1184_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__2(v___x_1183_, v_initializationOptions_x3f_1173_);
v___x_1185_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4));
v___x_1186_ = l_Lean_Lsp_instToJsonClientCapabilities_toJson(v_capabilities_1174_);
v___x_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1185_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = lean_box(0);
v___x_1189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__5));
switch(v_trace_1175_)
{
case 0:
{
lean_object* v___x_1207_; 
v___x_1207_ = ((lean_object*)(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__0));
v___y_1192_ = v___x_1207_;
goto v___jp_1191_;
}
case 1:
{
lean_object* v___x_1208_; 
v___x_1208_ = ((lean_object*)(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__1));
v___y_1192_ = v___x_1208_;
goto v___jp_1191_;
}
default: 
{
lean_object* v___x_1209_; 
v___x_1209_ = ((lean_object*)(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__2));
v___y_1192_ = v___x_1209_;
goto v___jp_1191_;
}
}
v___jp_1191_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_inc(v___y_1192_);
v___x_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1190_);
lean_ctor_set(v___x_1193_, 1, v___y_1192_);
v___x_1194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
lean_ctor_set(v___x_1194_, 1, v___x_1188_);
v___x_1195_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__6));
v___x_1196_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3(v___x_1195_, v_workspaceFolders_x3f_1176_);
v___x_1197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set(v___x_1197_, 1, v___x_1188_);
v___x_1198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1194_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1189_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1184_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1182_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1180_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1178_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2));
v___x_1205_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_1203_, v___x_1204_);
v___x_1206_ = l_Lean_Json_mkObj(v___x_1205_);
return v___x_1206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializeParams___lam__0(lean_object* v___x_1212_, lean_object* v___x_1213_, lean_object* v___x_1214_, lean_object* v___x_1215_, lean_object* v___x_1216_, lean_object* v___x_1217_, lean_object* v___f_1218_, lean_object* v_j_1219_){
_start:
{
lean_object* v___x_1220_; lean_object* v_processId_x3f_1221_; lean_object* v___x_1222_; lean_object* v_clientInfo_x3f_1223_; lean_object* v___x_1224_; lean_object* v_rootUri_x3f_1225_; lean_object* v___x_1226_; lean_object* v_initializationOptions_x3f_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1220_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__0));
lean_inc_n(v_j_1219_, 5);
v_processId_x3f_1221_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1219_, v___x_1212_, v___x_1220_);
v___x_1222_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__1));
v_clientInfo_x3f_1223_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1219_, v___x_1213_, v___x_1222_);
v___x_1224_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__2));
v_rootUri_x3f_1225_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1219_, v___x_1214_, v___x_1224_);
v___x_1226_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__3));
v_initializationOptions_x3f_1227_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1219_, v___x_1215_, v___x_1226_);
v___x_1228_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4));
v___x_1229_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1219_, v___x_1216_, v___x_1228_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
lean_dec_ref(v_initializationOptions_x3f_1227_);
lean_dec_ref(v_rootUri_x3f_1225_);
lean_dec_ref(v_clientInfo_x3f_1223_);
lean_dec_ref(v_processId_x3f_1221_);
lean_dec(v_j_1219_);
lean_dec_ref(v___f_1218_);
lean_dec_ref(v___x_1217_);
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1229_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1229_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
else
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1329_; 
v_a_1238_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1240_ = v___x_1229_;
v_isShared_1241_ = v_isSharedCheck_1329_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1229_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1329_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
uint8_t v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1254_; uint8_t v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1270_; uint8_t v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1285_; uint8_t v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1299_; uint8_t v___y_1300_; lean_object* v___y_1301_; uint8_t v___y_1312_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__5));
lean_inc(v_j_1219_);
v___x_1325_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1219_, v___f_1218_, v___x_1324_);
if (lean_obj_tag(v___x_1325_) == 0)
{
uint8_t v___x_1326_; 
lean_dec_ref(v___x_1325_);
v___x_1326_ = 0;
v___y_1312_ = v___x_1326_;
goto v___jp_1311_;
}
else
{
lean_object* v_a_1327_; uint8_t v___x_1328_; 
v_a_1327_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1327_);
lean_dec_ref(v___x_1325_);
v___x_1328_ = lean_unbox(v_a_1327_);
lean_dec(v_a_1327_);
v___y_1312_ = v___x_1328_;
goto v___jp_1311_;
}
v___jp_1242_:
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1249_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1249_, 0, v___y_1247_);
lean_ctor_set(v___x_1249_, 1, v___y_1246_);
lean_ctor_set(v___x_1249_, 2, v___y_1245_);
lean_ctor_set(v___x_1249_, 3, v___y_1244_);
lean_ctor_set(v___x_1249_, 4, v_a_1238_);
lean_ctor_set(v___x_1249_, 5, v___y_1248_);
lean_ctor_set_uint8(v___x_1249_, sizeof(void*)*6, v___y_1243_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 0, v___x_1249_);
v___x_1251_ = v___x_1240_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
v___jp_1253_:
{
if (lean_obj_tag(v___y_1254_) == 0)
{
lean_object* v___x_1260_; 
lean_dec_ref(v___y_1254_);
v___x_1260_ = lean_box(0);
v___y_1243_ = v___y_1255_;
v___y_1244_ = v___y_1259_;
v___y_1245_ = v___y_1256_;
v___y_1246_ = v___y_1257_;
v___y_1247_ = v___y_1258_;
v___y_1248_ = v___x_1260_;
goto v___jp_1242_;
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
v_a_1261_ = lean_ctor_get(v___y_1254_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___y_1254_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___y_1254_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___y_1254_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
v___y_1243_ = v___y_1255_;
v___y_1244_ = v___y_1259_;
v___y_1245_ = v___y_1256_;
v___y_1246_ = v___y_1257_;
v___y_1247_ = v___y_1258_;
v___y_1248_ = v___x_1266_;
goto v___jp_1242_;
}
}
}
}
v___jp_1269_:
{
if (lean_obj_tag(v_initializationOptions_x3f_1227_) == 0)
{
lean_object* v___x_1275_; 
lean_dec_ref(v_initializationOptions_x3f_1227_);
v___x_1275_ = lean_box(0);
v___y_1254_ = v___y_1270_;
v___y_1255_ = v___y_1271_;
v___y_1256_ = v___y_1274_;
v___y_1257_ = v___y_1272_;
v___y_1258_ = v___y_1273_;
v___y_1259_ = v___x_1275_;
goto v___jp_1253_;
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
v_a_1276_ = lean_ctor_get(v_initializationOptions_x3f_1227_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_initializationOptions_x3f_1227_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v_initializationOptions_x3f_1227_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v_initializationOptions_x3f_1227_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
v___y_1254_ = v___y_1270_;
v___y_1255_ = v___y_1271_;
v___y_1256_ = v___y_1274_;
v___y_1257_ = v___y_1272_;
v___y_1258_ = v___y_1273_;
v___y_1259_ = v___x_1281_;
goto v___jp_1253_;
}
}
}
}
v___jp_1284_:
{
if (lean_obj_tag(v_rootUri_x3f_1225_) == 0)
{
lean_object* v___x_1289_; 
lean_dec_ref(v_rootUri_x3f_1225_);
v___x_1289_ = lean_box(0);
v___y_1270_ = v___y_1285_;
v___y_1271_ = v___y_1286_;
v___y_1272_ = v___y_1288_;
v___y_1273_ = v___y_1287_;
v___y_1274_ = v___x_1289_;
goto v___jp_1269_;
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
v_a_1290_ = lean_ctor_get(v_rootUri_x3f_1225_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_rootUri_x3f_1225_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v_rootUri_x3f_1225_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v_rootUri_x3f_1225_);
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
v___y_1270_ = v___y_1285_;
v___y_1271_ = v___y_1286_;
v___y_1272_ = v___y_1288_;
v___y_1273_ = v___y_1287_;
v___y_1274_ = v___x_1295_;
goto v___jp_1269_;
}
}
}
}
v___jp_1298_:
{
if (lean_obj_tag(v_clientInfo_x3f_1223_) == 0)
{
lean_object* v___x_1302_; 
lean_dec_ref(v_clientInfo_x3f_1223_);
v___x_1302_ = lean_box(0);
v___y_1285_ = v___y_1299_;
v___y_1286_ = v___y_1300_;
v___y_1287_ = v___y_1301_;
v___y_1288_ = v___x_1302_;
goto v___jp_1284_;
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
v_a_1303_ = lean_ctor_get(v_clientInfo_x3f_1223_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_clientInfo_x3f_1223_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v_clientInfo_x3f_1223_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v_clientInfo_x3f_1223_);
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
v___y_1285_ = v___y_1299_;
v___y_1286_ = v___y_1300_;
v___y_1287_ = v___y_1301_;
v___y_1288_ = v___x_1308_;
goto v___jp_1284_;
}
}
}
}
v___jp_1311_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__6));
v___x_1314_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1219_, v___x_1217_, v___x_1313_);
if (lean_obj_tag(v_processId_x3f_1221_) == 0)
{
lean_object* v___x_1315_; 
lean_dec_ref(v_processId_x3f_1221_);
v___x_1315_ = lean_box(0);
v___y_1299_ = v___x_1314_;
v___y_1300_ = v___y_1312_;
v___y_1301_ = v___x_1315_;
goto v___jp_1298_;
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
v_a_1316_ = lean_ctor_get(v_processId_x3f_1221_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_processId_x3f_1221_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v_processId_x3f_1221_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v_processId_x3f_1221_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
v___y_1299_ = v___x_1314_;
v___y_1300_ = v___y_1312_;
v___y_1301_ = v___x_1321_;
goto v___jp_1298_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_InitializedParams_toCtorIdx(lean_object* v_x_1345_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_unsigned_to_nat(0u);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializedParams___lam__0(lean_object* v_x_1349_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializedParams___lam__0___closed__0));
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializedParams___lam__0___boxed(lean_object* v_x_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Lean_Lsp_instFromJsonInitializedParams___lam__0(v_x_1351_);
lean_dec(v_x_1351_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonInitializedParams___lam__0(lean_object* v_x_1355_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_box(0);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonServerInfo_toJson(lean_object* v_x_1359_){
_start:
{
lean_object* v_name_1360_; lean_object* v_version_x3f_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1379_; 
v_name_1360_ = lean_ctor_get(v_x_1359_, 0);
v_version_x3f_1361_ = lean_ctor_get(v_x_1359_, 1);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_x_1359_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1363_ = v_x_1359_;
v_isShared_1364_ = v_isSharedCheck_1379_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_version_x3f_1361_);
lean_inc(v_name_1360_);
lean_dec(v_x_1359_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1379_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1365_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0));
v___x_1366_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1366_, 0, v_name_1360_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 1, v___x_1366_);
lean_ctor_set(v___x_1363_, 0, v___x_1365_);
v___x_1368_ = v___x_1363_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1369_ = lean_box(0);
v___x_1370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1368_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
v___x_1371_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1));
v___x_1372_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__0(v___x_1371_, v_version_x3f_1361_);
v___x_1373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
lean_ctor_set(v___x_1373_, 1, v___x_1369_);
v___x_1374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1370_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
v___x_1375_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2));
v___x_1376_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_1374_, v___x_1375_);
v___x_1377_ = l_Lean_Json_mkObj(v___x_1376_);
return v___x_1377_;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1387_ = 1;
v___x_1388_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1));
v___x_1389_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1388_, v___x_1387_);
return v___x_1389_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5));
v___x_1391_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2);
v___x_1392_ = lean_string_append(v___x_1391_, v___x_1390_);
return v___x_1392_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1393_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8, &l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8);
v___x_1394_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3);
v___x_1395_ = lean_string_append(v___x_1394_, v___x_1393_);
return v___x_1395_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1396_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_1397_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4);
v___x_1398_ = lean_string_append(v___x_1397_, v___x_1396_);
return v___x_1398_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1399_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14, &l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14);
v___x_1400_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3);
v___x_1401_ = lean_string_append(v___x_1400_, v___x_1399_);
return v___x_1401_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1402_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_1403_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6);
v___x_1404_ = lean_string_append(v___x_1403_, v___x_1402_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonServerInfo_fromJson(lean_object* v_json_1405_){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0));
lean_inc(v_json_1405_);
v___x_1407_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__0(v_json_1405_, v___x_1406_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1417_; 
lean_dec(v_json_1405_);
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1417_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1417_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1412_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5);
v___x_1413_ = lean_string_append(v___x_1412_, v_a_1408_);
lean_dec(v_a_1408_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v___x_1413_);
v___x_1415_ = v___x_1410_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
else
{
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec(v_json_1405_);
v_a_1418_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1407_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1407_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
lean_ctor_set_tag(v___x_1420_, 0);
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v_a_1426_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1426_);
lean_dec_ref(v___x_1407_);
v___x_1427_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1));
v___x_1428_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1(v_json_1405_, v___x_1427_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1438_; 
lean_dec(v_a_1426_);
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1438_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1438_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1433_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7);
v___x_1434_ = lean_string_append(v___x_1433_, v_a_1429_);
lean_dec(v_a_1429_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1434_);
v___x_1436_ = v___x_1431_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
else
{
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec(v_a_1426_);
v_a_1439_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1428_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1428_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set_tag(v___x_1441_, 0);
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1455_; 
v_a_1447_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1449_ = v___x_1428_;
v_isShared_1450_ = v_isSharedCheck_1455_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1428_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1455_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1451_, 0, v_a_1426_);
lean_ctor_set(v___x_1451_, 1, v_a_1447_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 0, v___x_1451_);
v___x_1453_ = v___x_1449_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeResult_toJson_spec__0(lean_object* v_k_1458_, lean_object* v_x_1459_){
_start:
{
if (lean_obj_tag(v_x_1459_) == 0)
{
lean_object* v___x_1460_; 
lean_dec_ref(v_k_1458_);
v___x_1460_ = lean_box(0);
return v___x_1460_;
}
else
{
lean_object* v_val_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v_val_1461_ = lean_ctor_get(v_x_1459_, 0);
lean_inc(v_val_1461_);
lean_dec_ref(v_x_1459_);
v___x_1462_ = l_Lean_Lsp_instToJsonServerInfo_toJson(v_val_1461_);
v___x_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1463_, 0, v_k_1458_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = lean_box(0);
v___x_1465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1463_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
return v___x_1465_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonInitializeResult_toJson(lean_object* v_x_1467_){
_start:
{
lean_object* v_capabilities_1468_; lean_object* v_serverInfo_x3f_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1487_; 
v_capabilities_1468_ = lean_ctor_get(v_x_1467_, 0);
v_serverInfo_x3f_1469_ = lean_ctor_get(v_x_1467_, 1);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_x_1467_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1471_ = v_x_1467_;
v_isShared_1472_ = v_isSharedCheck_1487_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_serverInfo_x3f_1469_);
lean_inc(v_capabilities_1468_);
lean_dec(v_x_1467_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1487_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1473_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4));
v___x_1474_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson(v_capabilities_1468_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 1, v___x_1474_);
lean_ctor_set(v___x_1471_, 0, v___x_1473_);
v___x_1476_ = v___x_1471_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1473_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1477_ = lean_box(0);
v___x_1478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1476_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeResult_toJson___closed__0));
v___x_1480_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeResult_toJson_spec__0(v___x_1479_, v_serverInfo_x3f_1469_);
v___x_1481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
lean_ctor_set(v___x_1481_, 1, v___x_1477_);
v___x_1482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1478_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___x_1483_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2));
v___x_1484_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_1482_, v___x_1483_);
v___x_1485_ = l_Lean_Json_mkObj(v___x_1484_);
return v___x_1485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0(lean_object* v_j_1490_, lean_object* v_k_1491_){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = l_Lean_Json_getObjValD(v_j_1490_, v_k_1491_);
v___x_1493_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson(v___x_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0___boxed(lean_object* v_j_1494_, lean_object* v_k_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0(v_j_1494_, v_k_1495_);
lean_dec_ref(v_k_1495_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1(lean_object* v_x_1499_){
_start:
{
if (lean_obj_tag(v_x_1499_) == 0)
{
lean_object* v___x_1500_; 
v___x_1500_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1___closed__0));
return v___x_1500_;
}
else
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_Lsp_instFromJsonServerInfo_fromJson(v_x_1499_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1501_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1501_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1518_; 
v_a_1510_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1512_ = v___x_1501_;
v_isShared_1513_ = v_isSharedCheck_1518_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1501_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1518_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1514_; lean_object* v___x_1516_; 
v___x_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1514_, 0, v_a_1510_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v___x_1514_);
v___x_1516_ = v___x_1512_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1(lean_object* v_j_1519_, lean_object* v_k_1520_){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = l_Lean_Json_getObjValD(v_j_1519_, v_k_1520_);
v___x_1522_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1(v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1___boxed(lean_object* v_j_1523_, lean_object* v_k_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1(v_j_1523_, v_k_1524_);
lean_dec_ref(v_k_1524_);
return v_res_1525_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1531_ = 1;
v___x_1532_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1));
v___x_1533_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1532_, v___x_1531_);
return v___x_1533_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1534_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5));
v___x_1535_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2);
v___x_1536_ = lean_string_append(v___x_1535_, v___x_1534_);
return v___x_1536_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1539_ = 1;
v___x_1540_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__4));
v___x_1541_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1540_, v___x_1539_);
return v___x_1541_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1542_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5);
v___x_1543_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3);
v___x_1544_ = lean_string_append(v___x_1543_, v___x_1542_);
return v___x_1544_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1545_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_1546_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6);
v___x_1547_ = lean_string_append(v___x_1546_, v___x_1545_);
return v___x_1547_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10(void){
_start:
{
uint8_t v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1551_ = 1;
v___x_1552_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__9));
v___x_1553_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1552_, v___x_1551_);
return v___x_1553_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1554_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10);
v___x_1555_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3);
v___x_1556_ = lean_string_append(v___x_1555_, v___x_1554_);
return v___x_1556_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_1558_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11);
v___x_1559_ = lean_string_append(v___x_1558_, v___x_1557_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializeResult_fromJson(lean_object* v_json_1560_){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4));
lean_inc(v_json_1560_);
v___x_1562_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0(v_json_1560_, v___x_1561_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1572_; 
lean_dec(v_json_1560_);
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1565_ = v___x_1562_;
v_isShared_1566_ = v_isSharedCheck_1572_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1572_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1567_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7);
v___x_1568_ = lean_string_append(v___x_1567_, v_a_1563_);
lean_dec(v_a_1563_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v___x_1568_);
v___x_1570_ = v___x_1565_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
else
{
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec(v_json_1560_);
v_a_1573_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1562_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1562_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
lean_ctor_set_tag(v___x_1575_, 0);
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v_a_1581_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1581_);
lean_dec_ref(v___x_1562_);
v___x_1582_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeResult_toJson___closed__0));
v___x_1583_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1(v_json_1560_, v___x_1582_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1593_; 
lean_dec(v_a_1581_);
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1586_ = v___x_1583_;
v_isShared_1587_ = v_isSharedCheck_1593_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1593_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
v___x_1588_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12);
v___x_1589_ = lean_string_append(v___x_1588_, v_a_1584_);
lean_dec(v_a_1584_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1589_);
v___x_1591_ = v___x_1586_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
else
{
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec(v_a_1581_);
v_a_1594_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1583_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1583_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set_tag(v___x_1596_, 0);
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1610_; 
v_a_1602_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1604_ = v___x_1583_;
v_isShared_1605_ = v_isSharedCheck_1610_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1583_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1610_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1606_, 0, v_a_1581_);
lean_ctor_set(v___x_1606_, 1, v_a_1602_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1606_);
v___x_1608_ = v___x_1604_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_InitShutdown(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
