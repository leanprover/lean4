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
lean_object* l_Except_instMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* l_Except_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorIdx___impl___boxed(lean_object*);
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
static const lean_closure_object l_Lean_Lsp_instFromJsonHashSet___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonHashSet___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___redArg___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___closed__1_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonHashSet___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___redArg___lam__2___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonHashSet___redArg___closed__2_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonHashSet___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___redArg___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* v_a_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_a_136_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_a_136_);
lean_dec_ref_known(v___x_125_, 1);
v___x_137_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1));
v___x_138_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1(v_json_123_, v___x_137_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_148_; 
lean_dec(v_a_136_);
v_a_139_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_148_ == 0)
{
v___x_141_ = v___x_138_;
v_isShared_142_ = v_isSharedCheck_148_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_148_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_143_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__16, &l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__16);
v___x_144_ = lean_string_append(v___x_143_, v_a_139_);
lean_dec(v_a_139_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_144_);
v___x_146_ = v___x_141_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_157_; 
v_a_149_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_157_ == 0)
{
v___x_151_ = v___x_138_;
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_138_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_153_, 0, v_a_136_);
lean_ctor_set(v___x_153_, 1, v_a_149_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v___x_153_);
v___x_155_ = v___x_151_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorIdx___impl(uint8_t v_x_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_box(v_x_160_);
v___x_162_ = lean_obj_tag_nat(v___x_161_);
lean_dec(v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorIdx___impl___boxed(lean_object* v_x_163_){
_start:
{
uint8_t v_x_4__boxed_164_; lean_object* v_res_165_; 
v_x_4__boxed_164_ = lean_unbox(v_x_163_);
v_res_165_ = l_Lean_Lsp_Trace_ctorIdx___impl(v_x_4__boxed_164_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorElim___redArg(lean_object* v_k_166_){
_start:
{
lean_inc(v_k_166_);
return v_k_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorElim___redArg___boxed(lean_object* v_k_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Lsp_Trace_ctorElim___redArg(v_k_167_);
lean_dec(v_k_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorElim(lean_object* v_motive_169_, lean_object* v_ctorIdx_170_, uint8_t v_t_171_, lean_object* v_h_172_, lean_object* v_k_173_){
_start:
{
lean_inc(v_k_173_);
return v_k_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_ctorElim___boxed(lean_object* v_motive_174_, lean_object* v_ctorIdx_175_, lean_object* v_t_176_, lean_object* v_h_177_, lean_object* v_k_178_){
_start:
{
uint8_t v_t_boxed_179_; lean_object* v_res_180_; 
v_t_boxed_179_ = lean_unbox(v_t_176_);
v_res_180_ = l_Lean_Lsp_Trace_ctorElim(v_motive_174_, v_ctorIdx_175_, v_t_boxed_179_, v_h_177_, v_k_178_);
lean_dec(v_k_178_);
lean_dec(v_ctorIdx_175_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_off_elim___redArg(lean_object* v_off_181_){
_start:
{
lean_inc(v_off_181_);
return v_off_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_off_elim___redArg___boxed(lean_object* v_off_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_Lsp_Trace_off_elim___redArg(v_off_182_);
lean_dec(v_off_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_off_elim(lean_object* v_motive_184_, uint8_t v_t_185_, lean_object* v_h_186_, lean_object* v_off_187_){
_start:
{
lean_inc(v_off_187_);
return v_off_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_off_elim___boxed(lean_object* v_motive_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_off_191_){
_start:
{
uint8_t v_t_boxed_192_; lean_object* v_res_193_; 
v_t_boxed_192_ = lean_unbox(v_t_189_);
v_res_193_ = l_Lean_Lsp_Trace_off_elim(v_motive_188_, v_t_boxed_192_, v_h_190_, v_off_191_);
lean_dec(v_off_191_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_messages_elim___redArg(lean_object* v_messages_194_){
_start:
{
lean_inc(v_messages_194_);
return v_messages_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_messages_elim___redArg___boxed(lean_object* v_messages_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_Lsp_Trace_messages_elim___redArg(v_messages_195_);
lean_dec(v_messages_195_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_messages_elim(lean_object* v_motive_197_, uint8_t v_t_198_, lean_object* v_h_199_, lean_object* v_messages_200_){
_start:
{
lean_inc(v_messages_200_);
return v_messages_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_messages_elim___boxed(lean_object* v_motive_201_, lean_object* v_t_202_, lean_object* v_h_203_, lean_object* v_messages_204_){
_start:
{
uint8_t v_t_boxed_205_; lean_object* v_res_206_; 
v_t_boxed_205_ = lean_unbox(v_t_202_);
v_res_206_ = l_Lean_Lsp_Trace_messages_elim(v_motive_201_, v_t_boxed_205_, v_h_203_, v_messages_204_);
lean_dec(v_messages_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_verbose_elim___redArg(lean_object* v_verbose_207_){
_start:
{
lean_inc(v_verbose_207_);
return v_verbose_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_verbose_elim___redArg___boxed(lean_object* v_verbose_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Lsp_Trace_verbose_elim___redArg(v_verbose_208_);
lean_dec(v_verbose_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_verbose_elim(lean_object* v_motive_210_, uint8_t v_t_211_, lean_object* v_h_212_, lean_object* v_verbose_213_){
_start:
{
lean_inc(v_verbose_213_);
return v_verbose_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_verbose_elim___boxed(lean_object* v_motive_214_, lean_object* v_t_215_, lean_object* v_h_216_, lean_object* v_verbose_217_){
_start:
{
uint8_t v_t_boxed_218_; lean_object* v_res_219_; 
v_t_boxed_218_ = lean_unbox(v_t_215_);
v_res_219_ = l_Lean_Lsp_Trace_verbose_elim(v_motive_214_, v_t_boxed_218_, v_h_216_, v_verbose_217_);
lean_dec(v_verbose_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTrace___lam__0(lean_object* v_j_235_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_Json_getStr_x3f(v_j_235_);
if (lean_obj_tag(v___x_238_) == 1)
{
lean_object* v_a_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_a_239_);
lean_dec_ref_known(v___x_238_, 1);
v___x_240_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__2));
v___x_241_ = lean_string_dec_eq(v_a_239_, v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__3));
v___x_243_ = lean_string_dec_eq(v_a_239_, v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__4));
v___x_245_ = lean_string_dec_eq(v_a_239_, v___x_244_);
lean_dec(v_a_239_);
if (v___x_245_ == 0)
{
goto v___jp_236_;
}
else
{
lean_object* v___x_246_; 
v___x_246_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__5));
return v___x_246_;
}
}
else
{
lean_object* v___x_247_; 
lean_dec(v_a_239_);
v___x_247_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__6));
return v___x_247_;
}
}
else
{
lean_object* v___x_248_; 
lean_dec(v_a_239_);
v___x_248_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__7));
return v___x_248_;
}
}
else
{
lean_dec_ref(v___x_238_);
goto v___jp_236_;
}
v___jp_236_:
{
lean_object* v___x_237_; 
v___x_237_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__1));
return v___x_237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_hasToJson___lam__0(uint8_t v_x_257_){
_start:
{
switch(v_x_257_)
{
case 0:
{
lean_object* v___x_258_; 
v___x_258_ = ((lean_object*)(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__0));
return v___x_258_;
}
case 1:
{
lean_object* v___x_259_; 
v___x_259_ = ((lean_object*)(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__1));
return v___x_259_;
}
default: 
{
lean_object* v___x_260_; 
v___x_260_ = ((lean_object*)(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__2));
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Trace_hasToJson___lam__0___boxed(lean_object* v_x_261_){
_start:
{
uint8_t v_x_54__boxed_262_; lean_object* v_res_263_; 
v_x_54__boxed_262_ = lean_unbox(v_x_261_);
v_res_263_ = l_Lean_Lsp_Trace_hasToJson___lam__0(v_x_54__boxed_262_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__0(lean_object* v_x1_266_, lean_object* v_x2_267_, lean_object* v_x3_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = lean_array_push(v_x1_266_, v_x2_267_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__1(lean_object* v_inst_270_, lean_object* v_x_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = lean_apply_1(v_inst_270_, v_x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__2(lean_object* v___x_273_, lean_object* v___f_274_, lean_object* v_acc_275_, lean_object* v_l_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_273_, v___f_274_, v_acc_275_, v_l_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg___lam__3(lean_object* v___f_297_, lean_object* v___f_298_, lean_object* v_s_299_){
_start:
{
lean_object* v___y_301_; lean_object* v_size_307_; lean_object* v_buckets_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v_size_307_ = lean_ctor_get(v_s_299_, 0);
lean_inc(v_size_307_);
v_buckets_308_ = lean_ctor_get(v_s_299_, 1);
lean_inc_ref(v_buckets_308_);
lean_dec_ref(v_s_299_);
v___x_309_ = lean_mk_empty_array_with_capacity(v_size_307_);
lean_dec(v_size_307_);
v___x_310_ = ((lean_object*)(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__9));
v___x_311_ = lean_unsigned_to_nat(0u);
v___x_312_ = lean_array_get_size(v_buckets_308_);
v___x_313_ = lean_nat_dec_lt(v___x_311_, v___x_312_);
if (v___x_313_ == 0)
{
lean_dec_ref(v_buckets_308_);
lean_dec_ref(v___f_298_);
v___y_301_ = v___x_309_;
goto v___jp_300_;
}
else
{
lean_object* v___f_314_; size_t v___x_315_; size_t v___x_316_; lean_object* v___x_317_; 
v___f_314_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonHashSet___redArg___lam__2), 4, 2);
lean_closure_set(v___f_314_, 0, v___x_310_);
lean_closure_set(v___f_314_, 1, v___f_298_);
v___x_315_ = ((size_t)0ULL);
v___x_316_ = lean_usize_of_nat(v___x_312_);
v___x_317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_310_, v___f_314_, v_buckets_308_, v___x_315_, v___x_316_, v___x_309_);
v___y_301_ = v___x_317_;
goto v___jp_300_;
}
v___jp_300_:
{
lean_object* v___x_302_; size_t v_sz_303_; size_t v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_302_ = ((lean_object*)(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__9));
v_sz_303_ = lean_array_size(v___y_301_);
v___x_304_ = ((size_t)0ULL);
v___x_305_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_302_, v___f_297_, v_sz_303_, v___x_304_, v___y_301_);
v___x_306_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___redArg(lean_object* v_inst_319_){
_start:
{
lean_object* v___f_320_; lean_object* v___f_321_; lean_object* v___f_322_; 
v___f_320_ = ((lean_object*)(l_Lean_Lsp_instToJsonHashSet___redArg___closed__0));
v___f_321_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonHashSet___redArg___lam__1), 2, 1);
lean_closure_set(v___f_321_, 0, v_inst_319_);
v___f_322_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3), 3, 2);
lean_closure_set(v___f_322_, 0, v___f_321_);
lean_closure_set(v___f_322_, 1, v___f_320_);
return v___f_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet(lean_object* v_00_u03b1_323_, lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_inst_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Lsp_instToJsonHashSet___redArg(v_inst_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHashSet___boxed(lean_object* v_00_u03b1_328_, lean_object* v_inst_329_, lean_object* v_inst_330_, lean_object* v_inst_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_Lsp_instToJsonHashSet(v_00_u03b1_328_, v_inst_329_, v_inst_330_, v_inst_331_);
lean_dec_ref(v_inst_330_);
lean_dec_ref(v_inst_329_);
return v_res_332_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = lean_box(0);
v___x_338_ = lean_unsigned_to_nat(16u);
v___x_339_ = lean_mk_array(v___x_338_, v___x_337_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = lean_obj_once(&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2, &l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2_once, _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2);
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0(lean_object* v___x_346_, lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_x_350_){
_start:
{
if (lean_obj_tag(v_x_350_) == 4)
{
lean_object* v_elems_351_; size_t v_sz_352_; size_t v___x_353_; lean_object* v___x_354_; 
v_elems_351_ = lean_ctor_get(v_x_350_, 0);
lean_inc_ref(v_elems_351_);
lean_dec_ref_known(v_x_350_, 1);
v_sz_352_ = lean_array_size(v_elems_351_);
v___x_353_ = ((size_t)0ULL);
v___x_354_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_346_, v_inst_347_, v_sz_352_, v___x_353_, v_elems_351_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec_ref(v_inst_349_);
lean_dec_ref(v_inst_348_);
v_a_355_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_354_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_354_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_373_; 
v_a_363_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_373_ == 0)
{
v___x_365_ = v___x_354_;
v_isShared_366_ = v_isSharedCheck_373_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_354_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_373_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___f_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
v___f_367_ = ((lean_object*)(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__1));
v___x_368_ = lean_obj_once(&l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3, &l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3_once, _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3);
v___x_369_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_367_, v_inst_348_, v_inst_349_, v___x_368_, v_a_363_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v___x_369_);
v___x_371_ = v___x_365_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
else
{
lean_object* v___x_374_; 
lean_dec(v_x_350_);
lean_dec_ref(v_inst_349_);
lean_dec_ref(v_inst_348_);
lean_dec_ref(v_inst_347_);
lean_dec_ref(v___x_346_);
v___x_374_ = ((lean_object*)(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__5));
return v___x_374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHashSet___redArg(lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_inst_396_){
_start:
{
lean_object* v___x_397_; lean_object* v___f_398_; 
v___x_397_ = ((lean_object*)(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__9));
v___f_398_ = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0), 5, 4);
lean_closure_set(v___f_398_, 0, v___x_397_);
lean_closure_set(v___f_398_, 1, v_inst_396_);
lean_closure_set(v___f_398_, 2, v_inst_394_);
lean_closure_set(v___f_398_, 3, v_inst_395_);
return v___f_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHashSet(lean_object* v_00_u03b1_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_inst_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_Lsp_instFromJsonHashSet___redArg(v_inst_400_, v_inst_401_, v_inst_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0_spec__0(lean_object* v_x_404_){
_start:
{
if (lean_obj_tag(v_x_404_) == 0)
{
lean_object* v___x_405_; 
v___x_405_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1___closed__0));
return v___x_405_;
}
else
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Json_getStr_x3f(v_x_404_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_423_; 
v_a_415_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_423_ == 0)
{
v___x_417_ = v___x_406_;
v_isShared_418_ = v_isSharedCheck_423_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_406_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_423_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_419_, 0, v_a_415_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_419_);
v___x_421_ = v___x_417_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
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
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0(lean_object* v_j_424_, lean_object* v_k_425_){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = l_Lean_Json_getObjValD(v_j_424_, v_k_425_);
v___x_427_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0_spec__0(v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0___boxed(lean_object* v_j_428_, lean_object* v_k_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0(v_j_428_, v_k_429_);
lean_dec_ref(v_k_429_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10___redArg(lean_object* v_x_431_, lean_object* v_x_432_){
_start:
{
if (lean_obj_tag(v_x_432_) == 0)
{
return v_x_431_;
}
else
{
lean_object* v_key_433_; lean_object* v_value_434_; lean_object* v_tail_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_458_; 
v_key_433_ = lean_ctor_get(v_x_432_, 0);
v_value_434_ = lean_ctor_get(v_x_432_, 1);
v_tail_435_ = lean_ctor_get(v_x_432_, 2);
v_isSharedCheck_458_ = !lean_is_exclusive(v_x_432_);
if (v_isSharedCheck_458_ == 0)
{
v___x_437_ = v_x_432_;
v_isShared_438_ = v_isSharedCheck_458_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_tail_435_);
lean_inc(v_value_434_);
lean_inc(v_key_433_);
lean_dec(v_x_432_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_458_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; uint64_t v___x_440_; uint64_t v___x_441_; uint64_t v___x_442_; uint64_t v_fold_443_; uint64_t v___x_444_; uint64_t v___x_445_; uint64_t v___x_446_; size_t v___x_447_; size_t v___x_448_; size_t v___x_449_; size_t v___x_450_; size_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_439_ = lean_array_get_size(v_x_431_);
v___x_440_ = lean_string_hash(v_key_433_);
v___x_441_ = 32ULL;
v___x_442_ = lean_uint64_shift_right(v___x_440_, v___x_441_);
v_fold_443_ = lean_uint64_xor(v___x_440_, v___x_442_);
v___x_444_ = 16ULL;
v___x_445_ = lean_uint64_shift_right(v_fold_443_, v___x_444_);
v___x_446_ = lean_uint64_xor(v_fold_443_, v___x_445_);
v___x_447_ = lean_uint64_to_usize(v___x_446_);
v___x_448_ = lean_usize_of_nat(v___x_439_);
v___x_449_ = ((size_t)1ULL);
v___x_450_ = lean_usize_sub(v___x_448_, v___x_449_);
v___x_451_ = lean_usize_land(v___x_447_, v___x_450_);
v___x_452_ = lean_array_uget_borrowed(v_x_431_, v___x_451_);
lean_inc(v___x_452_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 2, v___x_452_);
v___x_454_ = v___x_437_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_key_433_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_value_434_);
lean_ctor_set(v_reuseFailAlloc_457_, 2, v___x_452_);
v___x_454_ = v_reuseFailAlloc_457_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_455_; 
v___x_455_ = lean_array_uset(v_x_431_, v___x_451_, v___x_454_);
v_x_431_ = v___x_455_;
v_x_432_ = v_tail_435_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8___redArg(lean_object* v_i_459_, lean_object* v_source_460_, lean_object* v_target_461_){
_start:
{
lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_462_ = lean_array_get_size(v_source_460_);
v___x_463_ = lean_nat_dec_lt(v_i_459_, v___x_462_);
if (v___x_463_ == 0)
{
lean_dec_ref(v_source_460_);
lean_dec(v_i_459_);
return v_target_461_;
}
else
{
lean_object* v_es_464_; lean_object* v___x_465_; lean_object* v_source_466_; lean_object* v_target_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v_es_464_ = lean_array_fget(v_source_460_, v_i_459_);
v___x_465_ = lean_box(0);
v_source_466_ = lean_array_fset(v_source_460_, v_i_459_, v___x_465_);
v_target_467_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10___redArg(v_target_461_, v_es_464_);
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = lean_nat_add(v_i_459_, v___x_468_);
lean_dec(v_i_459_);
v_i_459_ = v___x_469_;
v_source_460_ = v_source_466_;
v_target_461_ = v_target_467_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7___redArg(lean_object* v_data_471_){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v_nbuckets_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_472_ = lean_array_get_size(v_data_471_);
v___x_473_ = lean_unsigned_to_nat(2u);
v_nbuckets_474_ = lean_nat_mul(v___x_472_, v___x_473_);
v___x_475_ = lean_unsigned_to_nat(0u);
v___x_476_ = lean_box(0);
v___x_477_ = lean_mk_array(v_nbuckets_474_, v___x_476_);
v___x_478_ = lean_array_propagate_mark(v_data_471_, v___x_477_);
v___x_479_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8___redArg(v___x_475_, v_data_471_, v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_a_480_, lean_object* v_x_481_){
_start:
{
if (lean_obj_tag(v_x_481_) == 0)
{
uint8_t v___x_482_; 
v___x_482_ = 0;
return v___x_482_;
}
else
{
lean_object* v_key_483_; lean_object* v_tail_484_; uint8_t v___x_485_; 
v_key_483_ = lean_ctor_get(v_x_481_, 0);
v_tail_484_ = lean_ctor_get(v_x_481_, 2);
v___x_485_ = lean_string_dec_eq(v_key_483_, v_a_480_);
if (v___x_485_ == 0)
{
v_x_481_ = v_tail_484_;
goto _start;
}
else
{
return v___x_485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_a_487_, lean_object* v_x_488_){
_start:
{
uint8_t v_res_489_; lean_object* v_r_490_; 
v_res_489_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_a_487_, v_x_488_);
lean_dec(v_x_488_);
lean_dec_ref(v_a_487_);
v_r_490_ = lean_box(v_res_489_);
return v_r_490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_m_491_, lean_object* v_a_492_, lean_object* v_b_493_){
_start:
{
lean_object* v_size_494_; lean_object* v_buckets_495_; lean_object* v___x_496_; uint64_t v___x_497_; uint64_t v___x_498_; uint64_t v___x_499_; uint64_t v_fold_500_; uint64_t v___x_501_; uint64_t v___x_502_; uint64_t v___x_503_; size_t v___x_504_; size_t v___x_505_; size_t v___x_506_; size_t v___x_507_; size_t v___x_508_; lean_object* v_bkt_509_; uint8_t v___x_510_; 
v_size_494_ = lean_ctor_get(v_m_491_, 0);
v_buckets_495_ = lean_ctor_get(v_m_491_, 1);
v___x_496_ = lean_array_get_size(v_buckets_495_);
v___x_497_ = lean_string_hash(v_a_492_);
v___x_498_ = 32ULL;
v___x_499_ = lean_uint64_shift_right(v___x_497_, v___x_498_);
v_fold_500_ = lean_uint64_xor(v___x_497_, v___x_499_);
v___x_501_ = 16ULL;
v___x_502_ = lean_uint64_shift_right(v_fold_500_, v___x_501_);
v___x_503_ = lean_uint64_xor(v_fold_500_, v___x_502_);
v___x_504_ = lean_uint64_to_usize(v___x_503_);
v___x_505_ = lean_usize_of_nat(v___x_496_);
v___x_506_ = ((size_t)1ULL);
v___x_507_ = lean_usize_sub(v___x_505_, v___x_506_);
v___x_508_ = lean_usize_land(v___x_504_, v___x_507_);
v_bkt_509_ = lean_array_uget_borrowed(v_buckets_495_, v___x_508_);
v___x_510_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_a_492_, v_bkt_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_531_; 
lean_inc_ref(v_buckets_495_);
lean_inc(v_size_494_);
v_isSharedCheck_531_ = !lean_is_exclusive(v_m_491_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; lean_object* v_unused_533_; 
v_unused_532_ = lean_ctor_get(v_m_491_, 1);
lean_dec(v_unused_532_);
v_unused_533_ = lean_ctor_get(v_m_491_, 0);
lean_dec(v_unused_533_);
v___x_512_ = v_m_491_;
v_isShared_513_ = v_isSharedCheck_531_;
goto v_resetjp_511_;
}
else
{
lean_dec(v_m_491_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_531_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v_size_x27_515_; lean_object* v___x_516_; lean_object* v_buckets_x27_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_514_ = lean_unsigned_to_nat(1u);
v_size_x27_515_ = lean_nat_add(v_size_494_, v___x_514_);
lean_dec(v_size_494_);
lean_inc(v_bkt_509_);
v___x_516_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_516_, 0, v_a_492_);
lean_ctor_set(v___x_516_, 1, v_b_493_);
lean_ctor_set(v___x_516_, 2, v_bkt_509_);
v_buckets_x27_517_ = lean_array_uset(v_buckets_495_, v___x_508_, v___x_516_);
v___x_518_ = lean_unsigned_to_nat(4u);
v___x_519_ = lean_nat_mul(v_size_x27_515_, v___x_518_);
v___x_520_ = lean_unsigned_to_nat(3u);
v___x_521_ = lean_nat_div(v___x_519_, v___x_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_array_get_size(v_buckets_x27_517_);
v___x_523_ = lean_nat_dec_le(v___x_521_, v___x_522_);
lean_dec(v___x_521_);
if (v___x_523_ == 0)
{
lean_object* v_val_524_; lean_object* v___x_526_; 
v_val_524_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7___redArg(v_buckets_x27_517_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 1, v_val_524_);
lean_ctor_set(v___x_512_, 0, v_size_x27_515_);
v___x_526_ = v___x_512_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_size_x27_515_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_val_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
else
{
lean_object* v___x_529_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 1, v_buckets_x27_517_);
lean_ctor_set(v___x_512_, 0, v_size_x27_515_);
v___x_529_ = v___x_512_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_size_x27_515_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_buckets_x27_517_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
else
{
lean_dec(v_b_493_);
lean_dec_ref(v_a_492_);
return v_m_491_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6(lean_object* v_as_534_, size_t v_sz_535_, size_t v_i_536_, lean_object* v_b_537_){
_start:
{
uint8_t v___x_538_; 
v___x_538_ = lean_usize_dec_lt(v_i_536_, v_sz_535_);
if (v___x_538_ == 0)
{
return v_b_537_;
}
else
{
lean_object* v_a_539_; lean_object* v___x_540_; lean_object* v_r_541_; size_t v___x_542_; size_t v___x_543_; 
v_a_539_ = lean_array_uget_borrowed(v_as_534_, v_i_536_);
v___x_540_ = lean_box(0);
lean_inc(v_a_539_);
v_r_541_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(v_b_537_, v_a_539_, v___x_540_);
v___x_542_ = ((size_t)1ULL);
v___x_543_ = lean_usize_add(v_i_536_, v___x_542_);
v_i_536_ = v___x_543_;
v_b_537_ = v_r_541_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_as_545_, lean_object* v_sz_546_, lean_object* v_i_547_, lean_object* v_b_548_){
_start:
{
size_t v_sz_boxed_549_; size_t v_i_boxed_550_; lean_object* v_res_551_; 
v_sz_boxed_549_ = lean_unbox_usize(v_sz_546_);
lean_dec(v_sz_546_);
v_i_boxed_550_ = lean_unbox_usize(v_i_547_);
lean_dec(v_i_547_);
v_res_551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6(v_as_545_, v_sz_boxed_549_, v_i_boxed_550_, v_b_548_);
lean_dec_ref(v_as_545_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4(lean_object* v_m_552_, lean_object* v_l_553_){
_start:
{
size_t v_sz_554_; size_t v___x_555_; lean_object* v___x_556_; 
v_sz_554_ = lean_array_size(v_l_553_);
v___x_555_ = ((size_t)0ULL);
v___x_556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6(v_l_553_, v_sz_554_, v___x_555_, v_m_552_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4___boxed(lean_object* v_m_557_, lean_object* v_l_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4(v_m_557_, v_l_558_);
lean_dec_ref(v_l_558_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3(size_t v_sz_560_, size_t v_i_561_, lean_object* v_bs_562_){
_start:
{
uint8_t v___x_563_; 
v___x_563_ = lean_usize_dec_lt(v_i_561_, v_sz_560_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; 
v___x_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_564_, 0, v_bs_562_);
return v___x_564_;
}
else
{
lean_object* v_v_565_; lean_object* v___x_566_; 
v_v_565_ = lean_array_uget_borrowed(v_bs_562_, v_i_561_);
lean_inc(v_v_565_);
v___x_566_ = l_Lean_Json_getStr_x3f(v_v_565_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_dec_ref(v_bs_562_);
v_a_567_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_566_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_566_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
else
{
lean_object* v_a_575_; lean_object* v___x_576_; lean_object* v_bs_x27_577_; size_t v___x_578_; size_t v___x_579_; lean_object* v___x_580_; 
v_a_575_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v___x_566_, 1);
v___x_576_ = lean_unsigned_to_nat(0u);
v_bs_x27_577_ = lean_array_uset(v_bs_562_, v_i_561_, v___x_576_);
v___x_578_ = ((size_t)1ULL);
v___x_579_ = lean_usize_add(v_i_561_, v___x_578_);
v___x_580_ = lean_array_uset(v_bs_x27_577_, v_i_561_, v_a_575_);
v_i_561_ = v___x_579_;
v_bs_562_ = v___x_580_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3___boxed(lean_object* v_sz_582_, lean_object* v_i_583_, lean_object* v_bs_584_){
_start:
{
size_t v_sz_boxed_585_; size_t v_i_boxed_586_; lean_object* v_res_587_; 
v_sz_boxed_585_ = lean_unbox_usize(v_sz_582_);
lean_dec(v_sz_582_);
v_i_boxed_586_ = lean_unbox_usize(v_i_583_);
lean_dec(v_i_583_);
v_res_587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3(v_sz_boxed_585_, v_i_boxed_586_, v_bs_584_);
return v_res_587_;
}
}
static lean_object* _init_l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = lean_box(0);
v___x_591_ = lean_unsigned_to_nat(16u);
v___x_592_ = lean_mk_array(v___x_591_, v___x_590_);
return v___x_592_;
}
}
static lean_object* _init_l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_593_ = lean_obj_once(&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1, &l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1_once, _init_l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1);
v___x_594_ = lean_unsigned_to_nat(0u);
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___x_593_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2(lean_object* v_x_598_){
_start:
{
if (lean_obj_tag(v_x_598_) == 0)
{
lean_object* v___x_599_; 
v___x_599_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__0));
return v___x_599_;
}
else
{
if (lean_obj_tag(v_x_598_) == 4)
{
lean_object* v_elems_600_; size_t v_sz_601_; size_t v___x_602_; lean_object* v___x_603_; 
v_elems_600_ = lean_ctor_get(v_x_598_, 0);
lean_inc_ref(v_elems_600_);
lean_dec_ref_known(v_x_598_, 1);
v_sz_601_ = lean_array_size(v_elems_600_);
v___x_602_ = ((size_t)0ULL);
v___x_603_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3(v_sz_601_, v___x_602_, v_elems_600_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
v_a_604_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_603_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_603_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_622_; 
v_a_612_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_622_ == 0)
{
v___x_614_ = v___x_603_;
v_isShared_615_ = v_isSharedCheck_622_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_603_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_622_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_616_ = lean_obj_once(&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2, &l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2_once, _init_l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2);
v___x_617_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4(v___x_616_, v_a_612_);
lean_dec(v_a_612_);
v___x_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_618_);
v___x_620_ = v___x_614_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
else
{
lean_object* v___x_623_; 
lean_dec(v_x_598_);
v___x_623_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__3));
return v___x_623_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(lean_object* v_j_624_, lean_object* v_k_625_){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = l_Lean_Json_getObjValD(v_j_624_, v_k_625_);
v___x_627_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2(v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1___boxed(lean_object* v_j_628_, lean_object* v_k_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(v_j_628_, v_k_629_);
lean_dec_ref(v_k_629_);
return v_res_630_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3(void){
_start:
{
uint8_t v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = 1;
v___x_638_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2));
v___x_639_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_638_, v___x_637_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5));
v___x_641_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3);
v___x_642_ = lean_string_append(v___x_641_, v___x_640_);
return v___x_642_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7(void){
_start:
{
uint8_t v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = 1;
v___x_647_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__6));
v___x_648_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_647_, v___x_646_);
return v___x_648_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_649_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7);
v___x_650_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4);
v___x_651_ = lean_string_append(v___x_650_, v___x_649_);
return v___x_651_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_652_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_653_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8);
v___x_654_ = lean_string_append(v___x_653_, v___x_652_);
return v___x_654_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13(void){
_start:
{
uint8_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = 1;
v___x_660_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__12));
v___x_661_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_660_, v___x_659_);
return v___x_661_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_662_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13);
v___x_663_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4);
v___x_664_ = lean_string_append(v___x_663_, v___x_662_);
return v___x_664_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_666_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14);
v___x_667_ = lean_string_append(v___x_666_, v___x_665_);
return v___x_667_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19(void){
_start:
{
uint8_t v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_672_ = 1;
v___x_673_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__18));
v___x_674_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_673_, v___x_672_);
return v___x_674_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19);
v___x_676_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4);
v___x_677_ = lean_string_append(v___x_676_, v___x_675_);
return v___x_677_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_678_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_679_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20);
v___x_680_ = lean_string_append(v___x_679_, v___x_678_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLogConfig_fromJson(lean_object* v_json_681_){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__0));
lean_inc(v_json_681_);
v___x_683_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0(v_json_681_, v___x_682_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_693_; 
lean_dec(v_json_681_);
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_693_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_693_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_693_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_688_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9);
v___x_689_ = lean_string_append(v___x_688_, v_a_684_);
lean_dec(v_a_684_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_689_);
v___x_691_ = v___x_686_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
else
{
lean_object* v_a_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v_a_694_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v___x_683_, 1);
v___x_695_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__10));
lean_inc(v_json_681_);
v___x_696_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(v_json_681_, v___x_695_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_706_; 
lean_dec(v_a_694_);
lean_dec(v_json_681_);
v_a_697_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_706_ == 0)
{
v___x_699_ = v___x_696_;
v_isShared_700_ = v_isSharedCheck_706_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_696_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_706_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_701_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15);
v___x_702_ = lean_string_append(v___x_701_, v_a_697_);
lean_dec(v_a_697_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_702_);
v___x_704_ = v___x_699_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v_a_707_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_696_, 1);
v___x_708_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__16));
v___x_709_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(v_json_681_, v___x_708_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_719_; 
lean_dec(v_a_707_);
lean_dec(v_a_694_);
v_a_710_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_719_ == 0)
{
v___x_712_ = v___x_709_;
v_isShared_713_ = v_isSharedCheck_719_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_709_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_719_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_714_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21, &l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21_once, _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21);
v___x_715_ = lean_string_append(v___x_714_, v_a_710_);
lean_dec(v_a_710_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_715_);
v___x_717_ = v___x_712_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_728_; 
v_a_720_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_728_ == 0)
{
v___x_722_ = v___x_709_;
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_709_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_724_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_724_, 0, v_a_694_);
lean_ctor_set(v___x_724_, 1, v_a_707_);
lean_ctor_set(v___x_724_, 2, v_a_720_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_724_);
v___x_726_ = v___x_722_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_724_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_729_, lean_object* v_m_730_, lean_object* v_a_731_, lean_object* v_b_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(v_m_730_, v_a_731_, v_b_732_);
return v___x_733_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_734_, lean_object* v_a_735_, lean_object* v_x_736_){
_start:
{
uint8_t v___x_737_; 
v___x_737_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_a_735_, v_x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_00_u03b2_738_, lean_object* v_a_739_, lean_object* v_x_740_){
_start:
{
uint8_t v_res_741_; lean_object* v_r_742_; 
v_res_741_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6(v_00_u03b2_738_, v_a_739_, v_x_740_);
lean_dec(v_x_740_);
lean_dec_ref(v_a_739_);
v_r_742_ = lean_box(v_res_741_);
return v_r_742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7(lean_object* v_00_u03b2_743_, lean_object* v_data_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7___redArg(v_data_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8(lean_object* v_00_u03b2_746_, lean_object* v_i_747_, lean_object* v_source_748_, lean_object* v_target_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8___redArg(v_i_747_, v_source_748_, v_target_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10(lean_object* v_00_u03b2_751_, lean_object* v_x_752_, lean_object* v_x_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10___redArg(v_x_752_, v_x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__0(lean_object* v_k_757_, lean_object* v_x_758_){
_start:
{
if (lean_obj_tag(v_x_758_) == 0)
{
lean_object* v___x_759_; 
lean_dec_ref(v_k_757_);
v___x_759_ = lean_box(0);
return v___x_759_;
}
else
{
lean_object* v_val_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_770_; 
v_val_760_ = lean_ctor_get(v_x_758_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v_x_758_);
if (v_isSharedCheck_770_ == 0)
{
v___x_762_ = v_x_758_;
v_isShared_763_ = v_isSharedCheck_770_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_val_760_);
lean_dec(v_x_758_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_770_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set_tag(v___x_762_, 3);
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_val_760_);
v___x_765_ = v_reuseFailAlloc_769_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v_k_757_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = lean_box(0);
v___x_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_766_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
return v___x_768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1(size_t v_sz_771_, size_t v_i_772_, lean_object* v_bs_773_){
_start:
{
uint8_t v___x_774_; 
v___x_774_ = lean_usize_dec_lt(v_i_772_, v_sz_771_);
if (v___x_774_ == 0)
{
return v_bs_773_;
}
else
{
lean_object* v_v_775_; lean_object* v___x_776_; lean_object* v_bs_x27_777_; lean_object* v___x_778_; size_t v___x_779_; size_t v___x_780_; lean_object* v___x_781_; 
v_v_775_ = lean_array_uget(v_bs_773_, v_i_772_);
v___x_776_ = lean_unsigned_to_nat(0u);
v_bs_x27_777_ = lean_array_uset(v_bs_773_, v_i_772_, v___x_776_);
v___x_778_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_778_, 0, v_v_775_);
v___x_779_ = ((size_t)1ULL);
v___x_780_ = lean_usize_add(v_i_772_, v___x_779_);
v___x_781_ = lean_array_uset(v_bs_x27_777_, v_i_772_, v___x_778_);
v_i_772_ = v___x_780_;
v_bs_773_ = v___x_781_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1___boxed(lean_object* v_sz_783_, lean_object* v_i_784_, lean_object* v_bs_785_){
_start:
{
size_t v_sz_boxed_786_; size_t v_i_boxed_787_; lean_object* v_res_788_; 
v_sz_boxed_786_ = lean_unbox_usize(v_sz_783_);
lean_dec(v_sz_783_);
v_i_boxed_787_ = lean_unbox_usize(v_i_784_);
lean_dec(v_i_784_);
v_res_788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1(v_sz_boxed_786_, v_i_boxed_787_, v_bs_785_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__2(lean_object* v_x_789_, lean_object* v_x_790_){
_start:
{
if (lean_obj_tag(v_x_790_) == 0)
{
return v_x_789_;
}
else
{
lean_object* v_key_791_; lean_object* v_tail_792_; lean_object* v___x_793_; 
v_key_791_ = lean_ctor_get(v_x_790_, 0);
lean_inc(v_key_791_);
v_tail_792_ = lean_ctor_get(v_x_790_, 2);
lean_inc(v_tail_792_);
lean_dec_ref_known(v_x_790_, 3);
v___x_793_ = lean_array_push(v_x_789_, v_key_791_);
v_x_789_ = v___x_793_;
v_x_790_ = v_tail_792_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__3(lean_object* v_as_795_, size_t v_i_796_, size_t v_stop_797_, lean_object* v_b_798_){
_start:
{
uint8_t v___x_799_; 
v___x_799_ = lean_usize_dec_eq(v_i_796_, v_stop_797_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; lean_object* v___x_801_; size_t v___x_802_; size_t v___x_803_; 
v___x_800_ = lean_array_uget_borrowed(v_as_795_, v_i_796_);
lean_inc(v___x_800_);
v___x_801_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__2(v_b_798_, v___x_800_);
v___x_802_ = ((size_t)1ULL);
v___x_803_ = lean_usize_add(v_i_796_, v___x_802_);
v_i_796_ = v___x_803_;
v_b_798_ = v___x_801_;
goto _start;
}
else
{
return v_b_798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__3___boxed(lean_object* v_as_805_, lean_object* v_i_806_, lean_object* v_stop_807_, lean_object* v_b_808_){
_start:
{
size_t v_i_boxed_809_; size_t v_stop_boxed_810_; lean_object* v_res_811_; 
v_i_boxed_809_ = lean_unbox_usize(v_i_806_);
lean_dec(v_i_806_);
v_stop_boxed_810_ = lean_unbox_usize(v_stop_807_);
lean_dec(v_stop_807_);
v_res_811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__3(v_as_805_, v_i_boxed_809_, v_stop_boxed_810_, v_b_808_);
lean_dec_ref(v_as_805_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(lean_object* v_k_812_, lean_object* v_x_813_){
_start:
{
lean_object* v___y_815_; 
if (lean_obj_tag(v_x_813_) == 0)
{
lean_object* v___x_823_; 
lean_dec_ref(v_k_812_);
v___x_823_ = lean_box(0);
return v___x_823_;
}
else
{
lean_object* v_val_824_; lean_object* v_size_825_; lean_object* v_buckets_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v_val_824_ = lean_ctor_get(v_x_813_, 0);
v_size_825_ = lean_ctor_get(v_val_824_, 0);
v_buckets_826_ = lean_ctor_get(v_val_824_, 1);
v___x_827_ = lean_mk_empty_array_with_capacity(v_size_825_);
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = lean_array_get_size(v_buckets_826_);
v___x_830_ = lean_nat_dec_lt(v___x_828_, v___x_829_);
if (v___x_830_ == 0)
{
v___y_815_ = v___x_827_;
goto v___jp_814_;
}
else
{
size_t v___x_831_; size_t v___x_832_; lean_object* v___x_833_; 
v___x_831_ = ((size_t)0ULL);
v___x_832_ = lean_usize_of_nat(v___x_829_);
v___x_833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__3(v_buckets_826_, v___x_831_, v___x_832_, v___x_827_);
v___y_815_ = v___x_833_;
goto v___jp_814_;
}
}
v___jp_814_:
{
size_t v_sz_816_; size_t v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v_sz_816_ = lean_array_size(v___y_815_);
v___x_817_ = ((size_t)0ULL);
v___x_818_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1(v_sz_816_, v___x_817_, v___y_815_);
v___x_819_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v_k_812_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = lean_box(0);
v___x_822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_820_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
return v___x_822_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1___boxed(lean_object* v_k_834_, lean_object* v_x_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(v_k_834_, v_x_835_);
lean_dec(v_x_835_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLogConfig_toJson(lean_object* v_x_837_){
_start:
{
lean_object* v_logDir_x3f_838_; lean_object* v_allowedMethods_x3f_839_; lean_object* v_disallowedMethods_x3f_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_logDir_x3f_838_ = lean_ctor_get(v_x_837_, 0);
lean_inc(v_logDir_x3f_838_);
v_allowedMethods_x3f_839_ = lean_ctor_get(v_x_837_, 1);
lean_inc(v_allowedMethods_x3f_839_);
v_disallowedMethods_x3f_840_ = lean_ctor_get(v_x_837_, 2);
lean_inc(v_disallowedMethods_x3f_840_);
lean_dec_ref(v_x_837_);
v___x_841_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__0));
v___x_842_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__0(v___x_841_, v_logDir_x3f_838_);
v___x_843_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__10));
v___x_844_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(v___x_843_, v_allowedMethods_x3f_839_);
lean_dec(v_allowedMethods_x3f_839_);
v___x_845_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__16));
v___x_846_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(v___x_845_, v_disallowedMethods_x3f_840_);
lean_dec(v_disallowedMethods_x3f_840_);
v___x_847_ = lean_box(0);
v___x_848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_844_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_842_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2));
v___x_852_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_850_, v___x_851_);
v___x_853_ = l_Lean_Json_mkObj(v___x_852_);
lean_dec(v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0(lean_object* v_k_856_, lean_object* v_x_857_){
_start:
{
if (lean_obj_tag(v_x_857_) == 0)
{
lean_object* v___x_858_; 
lean_dec_ref(v_k_856_);
v___x_858_ = lean_box(0);
return v___x_858_;
}
else
{
lean_object* v_val_859_; lean_object* v___x_860_; uint8_t v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_val_859_ = lean_ctor_get(v_x_857_, 0);
v___x_860_ = lean_alloc_ctor(1, 0, 1);
v___x_861_ = lean_unbox(v_val_859_);
lean_ctor_set_uint8(v___x_860_, 0, v___x_861_);
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v_k_856_);
lean_ctor_set(v___x_862_, 1, v___x_860_);
v___x_863_ = lean_box(0);
v___x_864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0___boxed(lean_object* v_k_865_, lean_object* v_x_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0(v_k_865_, v_x_866_);
lean_dec(v_x_866_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__1(lean_object* v_k_868_, lean_object* v_x_869_){
_start:
{
if (lean_obj_tag(v_x_869_) == 0)
{
lean_object* v___x_870_; 
lean_dec_ref(v_k_868_);
v___x_870_ = lean_box(0);
return v___x_870_;
}
else
{
lean_object* v_val_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_val_871_ = lean_ctor_get(v_x_869_, 0);
lean_inc(v_val_871_);
lean_dec_ref_known(v_x_869_, 1);
v___x_872_ = l_Lean_Lsp_instToJsonLogConfig_toJson(v_val_871_);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v_k_868_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = lean_box(0);
v___x_875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_873_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
return v___x_875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonInitializationOptions_toJson(lean_object* v_x_878_){
_start:
{
lean_object* v_hasWidgets_x3f_879_; lean_object* v_logCfg_x3f_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_896_; 
v_hasWidgets_x3f_879_ = lean_ctor_get(v_x_878_, 0);
v_logCfg_x3f_880_ = lean_ctor_get(v_x_878_, 1);
v_isSharedCheck_896_ = !lean_is_exclusive(v_x_878_);
if (v_isSharedCheck_896_ == 0)
{
v___x_882_ = v_x_878_;
v_isShared_883_ = v_isSharedCheck_896_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_logCfg_x3f_880_);
lean_inc(v_hasWidgets_x3f_879_);
lean_dec(v_x_878_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_896_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_884_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__0));
v___x_885_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0(v___x_884_, v_hasWidgets_x3f_879_);
lean_dec(v_hasWidgets_x3f_879_);
v___x_886_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__1));
v___x_887_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__1(v___x_886_, v_logCfg_x3f_880_);
v___x_888_ = lean_box(0);
if (v_isShared_883_ == 0)
{
lean_ctor_set_tag(v___x_882_, 1);
lean_ctor_set(v___x_882_, 1, v___x_888_);
lean_ctor_set(v___x_882_, 0, v___x_887_);
v___x_890_ = v___x_882_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v___x_888_);
v___x_890_ = v_reuseFailAlloc_895_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_885_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2));
v___x_893_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_891_, v___x_892_);
v___x_894_ = l_Lean_Json_mkObj(v___x_893_);
lean_dec(v___x_893_);
return v___x_894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2(lean_object* v_x_901_){
_start:
{
if (lean_obj_tag(v_x_901_) == 0)
{
lean_object* v___x_902_; 
v___x_902_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2___closed__0));
return v___x_902_;
}
else
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_Lsp_instFromJsonLogConfig_fromJson(v_x_901_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_903_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_903_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_920_; 
v_a_912_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_920_ == 0)
{
v___x_914_ = v___x_903_;
v_isShared_915_ = v_isSharedCheck_920_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_903_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_920_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_916_, 0, v_a_912_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_916_);
v___x_918_ = v___x_914_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1(lean_object* v_j_921_, lean_object* v_k_922_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = l_Lean_Json_getObjValD(v_j_921_, v_k_922_);
v___x_924_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2(v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1___boxed(lean_object* v_j_925_, lean_object* v_k_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1(v_j_925_, v_k_926_);
lean_dec_ref(v_k_926_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0(lean_object* v_x_930_){
_start:
{
if (lean_obj_tag(v_x_930_) == 0)
{
lean_object* v___x_931_; 
v___x_931_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___closed__0));
return v___x_931_;
}
else
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_Json_getBool_x3f(v_x_930_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_932_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_932_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_949_; 
v_a_941_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_949_ == 0)
{
v___x_943_ = v___x_932_;
v_isShared_944_ = v_isSharedCheck_949_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_932_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_949_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_945_, 0, v_a_941_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_945_);
v___x_947_ = v___x_943_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_945_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___boxed(lean_object* v_x_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0(v_x_950_);
lean_dec(v_x_950_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0(lean_object* v_j_952_, lean_object* v_k_953_){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = l_Lean_Json_getObjValD(v_j_952_, v_k_953_);
v___x_955_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0(v___x_954_);
lean_dec(v___x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0___boxed(lean_object* v_j_956_, lean_object* v_k_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0(v_j_956_, v_k_957_);
lean_dec_ref(v_k_957_);
return v_res_958_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_964_ = 1;
v___x_965_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1));
v___x_966_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_965_, v___x_964_);
return v___x_966_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5));
v___x_968_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2);
v___x_969_ = lean_string_append(v___x_968_, v___x_967_);
return v___x_969_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6(void){
_start:
{
uint8_t v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = 1;
v___x_974_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__5));
v___x_975_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_974_, v___x_973_);
return v___x_975_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_976_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6);
v___x_977_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3);
v___x_978_ = lean_string_append(v___x_977_, v___x_976_);
return v___x_978_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_979_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_980_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7);
v___x_981_ = lean_string_append(v___x_980_, v___x_979_);
return v___x_981_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11(void){
_start:
{
uint8_t v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_985_ = 1;
v___x_986_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__10));
v___x_987_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_986_, v___x_985_);
return v___x_987_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_988_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11);
v___x_989_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3);
v___x_990_ = lean_string_append(v___x_989_, v___x_988_);
return v___x_990_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_991_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_992_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12);
v___x_993_ = lean_string_append(v___x_992_, v___x_991_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializationOptions_fromJson(lean_object* v_json_994_){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__0));
lean_inc(v_json_994_);
v___x_996_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0(v_json_994_, v___x_995_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1006_; 
lean_dec(v_json_994_);
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1006_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1006_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_1001_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8);
v___x_1002_ = lean_string_append(v___x_1001_, v_a_997_);
lean_dec(v_a_997_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1002_);
v___x_1004_ = v___x_999_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v_a_1007_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_1007_);
lean_dec_ref_known(v___x_996_, 1);
v___x_1008_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__1));
v___x_1009_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1(v_json_994_, v___x_1008_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1019_; 
lean_dec(v_a_1007_);
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1012_ = v___x_1009_;
v_isShared_1013_ = v_isSharedCheck_1019_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1009_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1019_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1014_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13, &l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13);
v___x_1015_ = lean_string_append(v___x_1014_, v_a_1010_);
lean_dec(v_a_1010_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v___x_1015_);
v___x_1017_ = v___x_1012_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1028_; 
v_a_1020_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1022_ = v___x_1009_;
v_isShared_1023_ = v_isSharedCheck_1028_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1009_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1028_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v_a_1007_);
lean_ctor_set(v___x_1024_, 1, v_a_1020_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1024_);
v___x_1026_ = v___x_1022_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__0(lean_object* v_k_1031_, lean_object* v_x_1032_){
_start:
{
if (lean_obj_tag(v_x_1032_) == 0)
{
lean_object* v___x_1033_; 
lean_dec_ref(v_k_1031_);
v___x_1033_ = lean_box(0);
return v___x_1033_;
}
else
{
lean_object* v_val_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1045_; 
v_val_1034_ = lean_ctor_get(v_x_1032_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_x_1032_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1036_ = v_x_1032_;
v_isShared_1037_ = v_isSharedCheck_1045_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_val_1034_);
lean_dec(v_x_1032_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1045_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1038_ = l_Lean_JsonNumber_fromInt(v_val_1034_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set_tag(v___x_1036_, 2);
lean_ctor_set(v___x_1036_, 0, v___x_1038_);
v___x_1040_ = v___x_1036_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v_k_1031_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = lean_box(0);
v___x_1043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1041_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
return v___x_1043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__1(lean_object* v_k_1046_, lean_object* v_x_1047_){
_start:
{
if (lean_obj_tag(v_x_1047_) == 0)
{
lean_object* v___x_1048_; 
lean_dec_ref(v_k_1046_);
v___x_1048_ = lean_box(0);
return v___x_1048_;
}
else
{
lean_object* v_val_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v_val_1049_ = lean_ctor_get(v_x_1047_, 0);
lean_inc(v_val_1049_);
lean_dec_ref_known(v_x_1047_, 1);
v___x_1050_ = l_Lean_Lsp_instToJsonClientInfo_toJson(v_val_1049_);
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v_k_1046_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = lean_box(0);
v___x_1053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1051_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
return v___x_1053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__2(lean_object* v_k_1054_, lean_object* v_x_1055_){
_start:
{
if (lean_obj_tag(v_x_1055_) == 0)
{
lean_object* v___x_1056_; 
lean_dec_ref(v_k_1054_);
v___x_1056_ = lean_box(0);
return v___x_1056_;
}
else
{
lean_object* v_val_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v_val_1057_ = lean_ctor_get(v_x_1055_, 0);
lean_inc(v_val_1057_);
lean_dec_ref_known(v_x_1055_, 1);
v___x_1058_ = l_Lean_Lsp_instToJsonInitializationOptions_toJson(v_val_1057_);
v___x_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1059_, 0, v_k_1054_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = lean_box(0);
v___x_1061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1059_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
return v___x_1061_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4(size_t v_sz_1062_, size_t v_i_1063_, lean_object* v_bs_1064_){
_start:
{
uint8_t v___x_1065_; 
v___x_1065_ = lean_usize_dec_lt(v_i_1063_, v_sz_1062_);
if (v___x_1065_ == 0)
{
return v_bs_1064_;
}
else
{
lean_object* v_v_1066_; lean_object* v___x_1067_; lean_object* v_bs_x27_1068_; lean_object* v___x_1069_; size_t v___x_1070_; size_t v___x_1071_; lean_object* v___x_1072_; 
v_v_1066_ = lean_array_uget(v_bs_1064_, v_i_1063_);
v___x_1067_ = lean_unsigned_to_nat(0u);
v_bs_x27_1068_ = lean_array_uset(v_bs_1064_, v_i_1063_, v___x_1067_);
v___x_1069_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson(v_v_1066_);
v___x_1070_ = ((size_t)1ULL);
v___x_1071_ = lean_usize_add(v_i_1063_, v___x_1070_);
v___x_1072_ = lean_array_uset(v_bs_x27_1068_, v_i_1063_, v___x_1069_);
v_i_1063_ = v___x_1071_;
v_bs_1064_ = v___x_1072_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_1074_, lean_object* v_i_1075_, lean_object* v_bs_1076_){
_start:
{
size_t v_sz_boxed_1077_; size_t v_i_boxed_1078_; lean_object* v_res_1079_; 
v_sz_boxed_1077_ = lean_unbox_usize(v_sz_1074_);
lean_dec(v_sz_1074_);
v_i_boxed_1078_ = lean_unbox_usize(v_i_1075_);
lean_dec(v_i_1075_);
v_res_1079_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4(v_sz_boxed_1077_, v_i_boxed_1078_, v_bs_1076_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3(lean_object* v_a_1080_){
_start:
{
size_t v_sz_1081_; size_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v_sz_1081_ = lean_array_size(v_a_1080_);
v___x_1082_ = ((size_t)0ULL);
v___x_1083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4(v_sz_1081_, v___x_1082_, v_a_1080_);
v___x_1084_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3(lean_object* v_k_1085_, lean_object* v_x_1086_){
_start:
{
if (lean_obj_tag(v_x_1086_) == 0)
{
lean_object* v___x_1087_; 
lean_dec_ref(v_k_1085_);
v___x_1087_ = lean_box(0);
return v___x_1087_;
}
else
{
lean_object* v_val_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v_val_1088_ = lean_ctor_get(v_x_1086_, 0);
lean_inc(v_val_1088_);
lean_dec_ref_known(v_x_1086_, 1);
v___x_1089_ = l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3(v_val_1088_);
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v_k_1085_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = lean_box(0);
v___x_1092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1090_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
return v___x_1092_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonInitializeParams_toJson(lean_object* v_x_1100_){
_start:
{
lean_object* v_processId_x3f_1101_; lean_object* v_clientInfo_x3f_1102_; lean_object* v_rootUri_x3f_1103_; lean_object* v_initializationOptions_x3f_1104_; lean_object* v_capabilities_1105_; uint8_t v_trace_1106_; lean_object* v_workspaceFolders_x3f_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___y_1123_; 
v_processId_x3f_1101_ = lean_ctor_get(v_x_1100_, 0);
lean_inc(v_processId_x3f_1101_);
v_clientInfo_x3f_1102_ = lean_ctor_get(v_x_1100_, 1);
lean_inc(v_clientInfo_x3f_1102_);
v_rootUri_x3f_1103_ = lean_ctor_get(v_x_1100_, 2);
lean_inc(v_rootUri_x3f_1103_);
v_initializationOptions_x3f_1104_ = lean_ctor_get(v_x_1100_, 3);
lean_inc(v_initializationOptions_x3f_1104_);
v_capabilities_1105_ = lean_ctor_get(v_x_1100_, 4);
lean_inc_ref(v_capabilities_1105_);
v_trace_1106_ = lean_ctor_get_uint8(v_x_1100_, sizeof(void*)*6);
v_workspaceFolders_x3f_1107_ = lean_ctor_get(v_x_1100_, 5);
lean_inc(v_workspaceFolders_x3f_1107_);
lean_dec_ref(v_x_1100_);
v___x_1108_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__0));
v___x_1109_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__0(v___x_1108_, v_processId_x3f_1101_);
v___x_1110_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__1));
v___x_1111_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__1(v___x_1110_, v_clientInfo_x3f_1102_);
v___x_1112_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__2));
v___x_1113_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__0(v___x_1112_, v_rootUri_x3f_1103_);
v___x_1114_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__3));
v___x_1115_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__2(v___x_1114_, v_initializationOptions_x3f_1104_);
v___x_1116_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4));
v___x_1117_ = l_Lean_Lsp_instToJsonClientCapabilities_toJson(v_capabilities_1105_);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = lean_box(0);
v___x_1120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1118_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__5));
switch(v_trace_1106_)
{
case 0:
{
lean_object* v___x_1138_; 
v___x_1138_ = ((lean_object*)(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__0));
v___y_1123_ = v___x_1138_;
goto v___jp_1122_;
}
case 1:
{
lean_object* v___x_1139_; 
v___x_1139_ = ((lean_object*)(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__1));
v___y_1123_ = v___x_1139_;
goto v___jp_1122_;
}
default: 
{
lean_object* v___x_1140_; 
v___x_1140_ = ((lean_object*)(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__2));
v___y_1123_ = v___x_1140_;
goto v___jp_1122_;
}
}
v___jp_1122_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_inc(v___y_1123_);
v___x_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1121_);
lean_ctor_set(v___x_1124_, 1, v___y_1123_);
v___x_1125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
lean_ctor_set(v___x_1125_, 1, v___x_1119_);
v___x_1126_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__6));
v___x_1127_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3(v___x_1126_, v_workspaceFolders_x3f_1107_);
v___x_1128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
lean_ctor_set(v___x_1128_, 1, v___x_1119_);
v___x_1129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1125_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1120_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1115_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1113_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1111_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
v___x_1134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1109_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2));
v___x_1136_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_1134_, v___x_1135_);
v___x_1137_ = l_Lean_Json_mkObj(v___x_1136_);
lean_dec(v___x_1136_);
return v___x_1137_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializeParams___lam__0(lean_object* v___x_1143_, lean_object* v___x_1144_, lean_object* v___x_1145_, lean_object* v___x_1146_, lean_object* v___x_1147_, lean_object* v___x_1148_, lean_object* v___f_1149_, lean_object* v_j_1150_){
_start:
{
lean_object* v___x_1151_; lean_object* v_processId_x3f_1152_; lean_object* v___x_1153_; lean_object* v_clientInfo_x3f_1154_; lean_object* v___x_1155_; lean_object* v_rootUri_x3f_1156_; lean_object* v___x_1157_; lean_object* v_initializationOptions_x3f_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1151_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__0));
lean_inc_n(v_j_1150_, 5);
v_processId_x3f_1152_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1150_, v___x_1143_, v___x_1151_);
v___x_1153_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__1));
v_clientInfo_x3f_1154_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1150_, v___x_1144_, v___x_1153_);
v___x_1155_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__2));
v_rootUri_x3f_1156_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1150_, v___x_1145_, v___x_1155_);
v___x_1157_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__3));
v_initializationOptions_x3f_1158_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1150_, v___x_1146_, v___x_1157_);
v___x_1159_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4));
v___x_1160_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1150_, v___x_1147_, v___x_1159_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_dec_ref(v_initializationOptions_x3f_1158_);
lean_dec_ref(v_rootUri_x3f_1156_);
lean_dec_ref(v_clientInfo_x3f_1154_);
lean_dec_ref(v_processId_x3f_1152_);
lean_dec(v_j_1150_);
lean_dec_ref(v___f_1149_);
lean_dec_ref(v___x_1148_);
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1160_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1260_; 
v_a_1169_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1171_ = v___x_1160_;
v_isShared_1172_ = v_isSharedCheck_1260_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1160_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1260_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___y_1174_; uint8_t v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1185_; uint8_t v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1201_; uint8_t v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; uint8_t v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; uint8_t v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; uint8_t v___y_1243_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__5));
lean_inc(v_j_1150_);
v___x_1256_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1150_, v___f_1149_, v___x_1255_);
if (lean_obj_tag(v___x_1256_) == 0)
{
uint8_t v___x_1257_; 
lean_dec_ref_known(v___x_1256_, 1);
v___x_1257_ = 0;
v___y_1243_ = v___x_1257_;
goto v___jp_1242_;
}
else
{
lean_object* v_a_1258_; uint8_t v___x_1259_; 
v_a_1258_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1258_);
lean_dec_ref_known(v___x_1256_, 1);
v___x_1259_ = lean_unbox(v_a_1258_);
lean_dec(v_a_1258_);
v___y_1243_ = v___x_1259_;
goto v___jp_1242_;
}
v___jp_1173_:
{
lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1180_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1180_, 0, v___y_1176_);
lean_ctor_set(v___x_1180_, 1, v___y_1174_);
lean_ctor_set(v___x_1180_, 2, v___y_1178_);
lean_ctor_set(v___x_1180_, 3, v___y_1177_);
lean_ctor_set(v___x_1180_, 4, v_a_1169_);
lean_ctor_set(v___x_1180_, 5, v___y_1179_);
lean_ctor_set_uint8(v___x_1180_, sizeof(void*)*6, v___y_1175_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1180_);
v___x_1182_ = v___x_1171_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1180_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
v___jp_1184_:
{
if (lean_obj_tag(v___y_1188_) == 0)
{
lean_object* v___x_1191_; 
lean_dec_ref_known(v___y_1188_, 1);
v___x_1191_ = lean_box(0);
v___y_1174_ = v___y_1185_;
v___y_1175_ = v___y_1186_;
v___y_1176_ = v___y_1187_;
v___y_1177_ = v___y_1190_;
v___y_1178_ = v___y_1189_;
v___y_1179_ = v___x_1191_;
goto v___jp_1173_;
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
v_a_1192_ = lean_ctor_get(v___y_1188_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___y_1188_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___y_1188_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___y_1188_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
v___y_1174_ = v___y_1185_;
v___y_1175_ = v___y_1186_;
v___y_1176_ = v___y_1187_;
v___y_1177_ = v___y_1190_;
v___y_1178_ = v___y_1189_;
v___y_1179_ = v___x_1197_;
goto v___jp_1173_;
}
}
}
}
v___jp_1200_:
{
if (lean_obj_tag(v_initializationOptions_x3f_1158_) == 0)
{
lean_object* v___x_1206_; 
lean_dec_ref_known(v_initializationOptions_x3f_1158_, 1);
v___x_1206_ = lean_box(0);
v___y_1185_ = v___y_1201_;
v___y_1186_ = v___y_1202_;
v___y_1187_ = v___y_1203_;
v___y_1188_ = v___y_1204_;
v___y_1189_ = v___y_1205_;
v___y_1190_ = v___x_1206_;
goto v___jp_1184_;
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
v_a_1207_ = lean_ctor_get(v_initializationOptions_x3f_1158_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_initializationOptions_x3f_1158_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v_initializationOptions_x3f_1158_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v_initializationOptions_x3f_1158_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
v___y_1185_ = v___y_1201_;
v___y_1186_ = v___y_1202_;
v___y_1187_ = v___y_1203_;
v___y_1188_ = v___y_1204_;
v___y_1189_ = v___y_1205_;
v___y_1190_ = v___x_1212_;
goto v___jp_1184_;
}
}
}
}
v___jp_1215_:
{
if (lean_obj_tag(v_rootUri_x3f_1156_) == 0)
{
lean_object* v___x_1220_; 
lean_dec_ref_known(v_rootUri_x3f_1156_, 1);
v___x_1220_ = lean_box(0);
v___y_1201_ = v___y_1219_;
v___y_1202_ = v___y_1216_;
v___y_1203_ = v___y_1217_;
v___y_1204_ = v___y_1218_;
v___y_1205_ = v___x_1220_;
goto v___jp_1200_;
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
v_a_1221_ = lean_ctor_get(v_rootUri_x3f_1156_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_rootUri_x3f_1156_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v_rootUri_x3f_1156_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v_rootUri_x3f_1156_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
v___y_1201_ = v___y_1219_;
v___y_1202_ = v___y_1216_;
v___y_1203_ = v___y_1217_;
v___y_1204_ = v___y_1218_;
v___y_1205_ = v___x_1226_;
goto v___jp_1200_;
}
}
}
}
v___jp_1229_:
{
if (lean_obj_tag(v_clientInfo_x3f_1154_) == 0)
{
lean_object* v___x_1233_; 
lean_dec_ref_known(v_clientInfo_x3f_1154_, 1);
v___x_1233_ = lean_box(0);
v___y_1216_ = v___y_1230_;
v___y_1217_ = v___y_1232_;
v___y_1218_ = v___y_1231_;
v___y_1219_ = v___x_1233_;
goto v___jp_1215_;
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
v_a_1234_ = lean_ctor_get(v_clientInfo_x3f_1154_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_clientInfo_x3f_1154_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v_clientInfo_x3f_1154_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v_clientInfo_x3f_1154_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
v___y_1216_ = v___y_1230_;
v___y_1217_ = v___y_1232_;
v___y_1218_ = v___y_1231_;
v___y_1219_ = v___x_1239_;
goto v___jp_1215_;
}
}
}
}
v___jp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__6));
v___x_1245_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1150_, v___x_1148_, v___x_1244_);
if (lean_obj_tag(v_processId_x3f_1152_) == 0)
{
lean_object* v___x_1246_; 
lean_dec_ref_known(v_processId_x3f_1152_, 1);
v___x_1246_ = lean_box(0);
v___y_1230_ = v___y_1243_;
v___y_1231_ = v___x_1245_;
v___y_1232_ = v___x_1246_;
goto v___jp_1229_;
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
v_a_1247_ = lean_ctor_get(v_processId_x3f_1152_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_processId_x3f_1152_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v_processId_x3f_1152_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v_processId_x3f_1152_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
v___y_1230_ = v___y_1243_;
v___y_1231_ = v___x_1245_;
v___y_1232_ = v___x_1252_;
goto v___jp_1229_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializedParams___lam__0(lean_object* v_x_1278_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializedParams___lam__0___closed__0));
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializedParams___lam__0___boxed(lean_object* v_x_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_Lsp_instFromJsonInitializedParams___lam__0(v_x_1280_);
lean_dec(v_x_1280_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonInitializedParams___lam__0(lean_object* v_x_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_box(0);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonServerInfo_toJson(lean_object* v_x_1288_){
_start:
{
lean_object* v_name_1289_; lean_object* v_version_x3f_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1308_; 
v_name_1289_ = lean_ctor_get(v_x_1288_, 0);
v_version_x3f_1290_ = lean_ctor_get(v_x_1288_, 1);
v_isSharedCheck_1308_ = !lean_is_exclusive(v_x_1288_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1292_ = v_x_1288_;
v_isShared_1293_ = v_isSharedCheck_1308_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_version_x3f_1290_);
lean_inc(v_name_1289_);
lean_dec(v_x_1288_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1308_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1297_; 
v___x_1294_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0));
v___x_1295_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1295_, 0, v_name_1289_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 1, v___x_1295_);
lean_ctor_set(v___x_1292_, 0, v___x_1294_);
v___x_1297_ = v___x_1292_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1294_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1298_ = lean_box(0);
v___x_1299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1297_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
v___x_1300_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1));
v___x_1301_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__0(v___x_1300_, v_version_x3f_1290_);
v___x_1302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v___x_1298_);
v___x_1303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1299_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
v___x_1304_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2));
v___x_1305_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_1303_, v___x_1304_);
v___x_1306_ = l_Lean_Json_mkObj(v___x_1305_);
lean_dec(v___x_1305_);
return v___x_1306_;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = 1;
v___x_1317_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1));
v___x_1318_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1317_, v___x_1316_);
return v___x_1318_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5));
v___x_1320_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2);
v___x_1321_ = lean_string_append(v___x_1320_, v___x_1319_);
return v___x_1321_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8, &l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8);
v___x_1323_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3);
v___x_1324_ = lean_string_append(v___x_1323_, v___x_1322_);
return v___x_1324_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1325_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_1326_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4);
v___x_1327_ = lean_string_append(v___x_1326_, v___x_1325_);
return v___x_1327_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1328_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14, &l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14);
v___x_1329_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3);
v___x_1330_ = lean_string_append(v___x_1329_, v___x_1328_);
return v___x_1330_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1331_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_1332_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6);
v___x_1333_ = lean_string_append(v___x_1332_, v___x_1331_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonServerInfo_fromJson(lean_object* v_json_1334_){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0));
lean_inc(v_json_1334_);
v___x_1336_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__0(v_json_1334_, v___x_1335_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1346_; 
lean_dec(v_json_1334_);
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1339_ = v___x_1336_;
v_isShared_1340_ = v_isSharedCheck_1346_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1336_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1346_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1344_; 
v___x_1341_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5);
v___x_1342_ = lean_string_append(v___x_1341_, v_a_1337_);
lean_dec(v_a_1337_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1342_);
v___x_1344_ = v___x_1339_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v_a_1347_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1347_);
lean_dec_ref_known(v___x_1336_, 1);
v___x_1348_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1));
v___x_1349_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1(v_json_1334_, v___x_1348_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1359_; 
lean_dec(v_a_1347_);
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1352_ = v___x_1349_;
v_isShared_1353_ = v_isSharedCheck_1359_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1359_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1354_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7, &l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7);
v___x_1355_ = lean_string_append(v___x_1354_, v_a_1350_);
lean_dec(v_a_1350_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1355_);
v___x_1357_ = v___x_1352_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1368_; 
v_a_1360_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1362_ = v___x_1349_;
v_isShared_1363_ = v_isSharedCheck_1368_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1349_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1368_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v_a_1347_);
lean_ctor_set(v___x_1364_, 1, v_a_1360_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v___x_1364_);
v___x_1366_ = v___x_1362_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeResult_toJson_spec__0(lean_object* v_k_1371_, lean_object* v_x_1372_){
_start:
{
if (lean_obj_tag(v_x_1372_) == 0)
{
lean_object* v___x_1373_; 
lean_dec_ref(v_k_1371_);
v___x_1373_ = lean_box(0);
return v___x_1373_;
}
else
{
lean_object* v_val_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v_val_1374_ = lean_ctor_get(v_x_1372_, 0);
lean_inc(v_val_1374_);
lean_dec_ref_known(v_x_1372_, 1);
v___x_1375_ = l_Lean_Lsp_instToJsonServerInfo_toJson(v_val_1374_);
v___x_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1376_, 0, v_k_1371_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
v___x_1377_ = lean_box(0);
v___x_1378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1376_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
return v___x_1378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonInitializeResult_toJson(lean_object* v_x_1380_){
_start:
{
lean_object* v_capabilities_1381_; lean_object* v_serverInfo_x3f_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1400_; 
v_capabilities_1381_ = lean_ctor_get(v_x_1380_, 0);
v_serverInfo_x3f_1382_ = lean_ctor_get(v_x_1380_, 1);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_x_1380_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1384_ = v_x_1380_;
v_isShared_1385_ = v_isSharedCheck_1400_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_serverInfo_x3f_1382_);
lean_inc(v_capabilities_1381_);
lean_dec(v_x_1380_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1400_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1386_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4));
v___x_1387_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson(v_capabilities_1381_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 1, v___x_1387_);
lean_ctor_set(v___x_1384_, 0, v___x_1386_);
v___x_1389_ = v___x_1384_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1390_ = lean_box(0);
v___x_1391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1389_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
v___x_1392_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeResult_toJson___closed__0));
v___x_1393_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeResult_toJson_spec__0(v___x_1392_, v_serverInfo_x3f_1382_);
v___x_1394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
lean_ctor_set(v___x_1394_, 1, v___x_1390_);
v___x_1395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1391_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
v___x_1396_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2));
v___x_1397_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_1395_, v___x_1396_);
v___x_1398_ = l_Lean_Json_mkObj(v___x_1397_);
lean_dec(v___x_1397_);
return v___x_1398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0(lean_object* v_j_1403_, lean_object* v_k_1404_){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = l_Lean_Json_getObjValD(v_j_1403_, v_k_1404_);
v___x_1406_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson(v___x_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0___boxed(lean_object* v_j_1407_, lean_object* v_k_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0(v_j_1407_, v_k_1408_);
lean_dec_ref(v_k_1408_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1(lean_object* v_x_1412_){
_start:
{
if (lean_obj_tag(v_x_1412_) == 0)
{
lean_object* v___x_1413_; 
v___x_1413_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1___closed__0));
return v___x_1413_;
}
else
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Lean_Lsp_instFromJsonServerInfo_fromJson(v_x_1412_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1431_; 
v_a_1423_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1425_ = v___x_1414_;
v_isShared_1426_ = v_isSharedCheck_1431_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1414_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1431_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1427_, 0, v_a_1423_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1427_);
v___x_1429_ = v___x_1425_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1(lean_object* v_j_1432_, lean_object* v_k_1433_){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = l_Lean_Json_getObjValD(v_j_1432_, v_k_1433_);
v___x_1435_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1(v___x_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1___boxed(lean_object* v_j_1436_, lean_object* v_k_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1(v_j_1436_, v_k_1437_);
lean_dec_ref(v_k_1437_);
return v_res_1438_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1444_ = 1;
v___x_1445_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1));
v___x_1446_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1445_, v___x_1444_);
return v___x_1446_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1447_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5));
v___x_1448_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2);
v___x_1449_ = lean_string_append(v___x_1448_, v___x_1447_);
return v___x_1449_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1452_ = 1;
v___x_1453_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__4));
v___x_1454_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1453_, v___x_1452_);
return v___x_1454_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1455_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5);
v___x_1456_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3);
v___x_1457_ = lean_string_append(v___x_1456_, v___x_1455_);
return v___x_1457_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_1459_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6);
v___x_1460_ = lean_string_append(v___x_1459_, v___x_1458_);
return v___x_1460_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10(void){
_start:
{
uint8_t v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1464_ = 1;
v___x_1465_ = ((lean_object*)(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__9));
v___x_1466_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1465_, v___x_1464_);
return v___x_1466_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1467_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10);
v___x_1468_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3);
v___x_1469_ = lean_string_append(v___x_1468_, v___x_1467_);
return v___x_1469_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1470_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10));
v___x_1471_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11);
v___x_1472_ = lean_string_append(v___x_1471_, v___x_1470_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonInitializeResult_fromJson(lean_object* v_json_1473_){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4));
lean_inc(v_json_1473_);
v___x_1475_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0(v_json_1473_, v___x_1474_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1485_; 
lean_dec(v_json_1473_);
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1485_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1485_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1483_; 
v___x_1480_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7);
v___x_1481_ = lean_string_append(v___x_1480_, v_a_1476_);
lean_dec(v_a_1476_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1481_);
v___x_1483_ = v___x_1478_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1481_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v_a_1486_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1486_);
lean_dec_ref_known(v___x_1475_, 1);
v___x_1487_ = ((lean_object*)(l_Lean_Lsp_instToJsonInitializeResult_toJson___closed__0));
v___x_1488_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1(v_json_1473_, v___x_1487_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1498_; 
lean_dec(v_a_1486_);
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1491_ = v___x_1488_;
v_isShared_1492_ = v_isSharedCheck_1498_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1488_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1498_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1493_ = lean_obj_once(&l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12, &l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12);
v___x_1494_ = lean_string_append(v___x_1493_, v_a_1489_);
lean_dec(v_a_1489_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v___x_1494_);
v___x_1496_ = v___x_1491_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1507_; 
v_a_1499_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1501_ = v___x_1488_;
v_isShared_1502_ = v_isSharedCheck_1507_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1488_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1507_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; lean_object* v___x_1505_; 
v___x_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1503_, 0, v_a_1486_);
lean_ctor_set(v___x_1503_, 1, v_a_1499_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v___x_1503_);
v___x_1505_ = v___x_1501_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
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
