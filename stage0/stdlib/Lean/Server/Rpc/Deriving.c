// Lean compiler output
// Module: Lean.Server.Rpc.Deriving
// Imports: public import Lean.Elab.Deriving.Basic
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
static const lean_string_object l_Lean_Server_RpcEncodable_isOptField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_Server_RpcEncodable_isOptField___closed__0 = (const lean_object*)&l_Lean_Server_RpcEncodable_isOptField___closed__0_value;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_once_cell_t l_Lean_Server_RpcEncodable_isOptField___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_RpcEncodable_isOptField___closed__1;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_RpcEncodable_isOptField(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RpcEncodable_isOptField___boxed(lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__2_value;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__5_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "structExplicitBinder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__8_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__8_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__7_value),LEAN_SCALAR_PTR_LITERAL(156, 255, 55, 101, 203, 12, 116, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__11_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__13_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__14_value;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__6(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "RpcEncodable"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Json"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__1_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__2;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(190, 18, 71, 130, 82, 255, 111, 18)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(215, 126, 99, 176, 35, 107, 201, 11)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__9_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__9_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__9_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__12_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__12_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__12_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(81, 102, 39, 227, 176, 252, 65, 103)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "liftMethod"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(217, 228, 135, 132, 46, 84, 105, 88)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rpcEncode"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(181, 130, 28, 14, 164, 108, 68, 133)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Server"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 192, 180, 137, 118, 34, 3, 132)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(147, 95, 3, 206, 143, 66, 59, 169)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__24_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__25_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__26 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__26_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__27_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__27_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__27_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__27_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__29;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__31 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__31_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__4_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__32 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__32_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__33 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__33_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__5_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__33_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__34 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__34_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rpcDecode"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__35 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__35_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(18, 61, 22, 59, 236, 209, 187, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 192, 180, 137, 118, 34, 3, 132)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(220, 0, 93, 28, 42, 216, 37, 123)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__40 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__40_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__42;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__43 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__43_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__43_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__44 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__44_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__45_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(54, 183, 132, 140, 253, 175, 101, 43)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__45 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__45_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__45_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__46 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__46_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__46_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__47 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__47_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__44_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__47_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__48 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__48_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__49 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__49_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__50 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__50_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__50_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__52 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__52_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__52_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__54 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__54_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__54_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 192, 180, 137, 118, 34, 3, 132)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__59_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__60 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__60_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__49_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__61_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__62 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__62_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__49_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__63_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__64 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__64_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__65_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__49_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__65 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__65_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__65_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__66 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__66_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__67 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__67_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__68_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__68 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__68_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__68_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__69 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__69_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__69_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__70 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__70_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__66_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__70_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__71 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__71_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__64_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__71_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__72 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__72_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__62_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__72_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__73 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__73_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__60_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__73_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__74 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__74_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__74_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__75 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__75_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mapM"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__76 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__76_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__77;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__76_value),LEAN_SCALAR_PTR_LITERAL(58, 78, 170, 251, 181, 31, 172, 28)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__78 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__78_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Deriving"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__0 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__49_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 131, 12, 184, 158, 202, 243, 28)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__1 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__1_value;
static const lean_array_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__2 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__2_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__3;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__4;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__5;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__6 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__6_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__6_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__8 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__8_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__8_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "structure"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__10 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__10_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__11_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__10_value),LEAN_SCALAR_PTR_LITERAL(180, 236, 187, 15, 83, 171, 117, 65)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__11 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__11_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "structureTk"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__12 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__12_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__12_value),LEAN_SCALAR_PTR_LITERAL(132, 164, 13, 167, 248, 219, 132, 242)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__14 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__14_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__14_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "RpcEncodablePacket"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__16 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__16_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__17;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__16_value),LEAN_SCALAR_PTR_LITERAL(59, 154, 188, 20, 17, 205, 207, 181)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__18 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__18_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "where"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__19 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__19_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "structFields"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__20 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__20_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__20_value),LEAN_SCALAR_PTR_LITERAL(162, 20, 124, 55, 90, 140, 156, 83)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optDeriving"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__22 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__22_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__23_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__23_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__23_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__22_value),LEAN_SCALAR_PTR_LITERAL(215, 163, 253, 206, 79, 89, 101, 240)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__23 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__23_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "deriving"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__24 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__24_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "derivingClass"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__25 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__25_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__25_value),LEAN_SCALAR_PTR_LITERAL(71, 164, 144, 68, 145, 86, 212, 243)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "FromJson"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__27 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__27_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__28;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__27_value),LEAN_SCALAR_PTR_LITERAL(9, 26, 128, 190, 189, 230, 248, 17)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__29 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__29_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__30_value_aux_0),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__27_value),LEAN_SCALAR_PTR_LITERAL(56, 129, 161, 88, 112, 64, 72, 138)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__30 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__30_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__31 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__31_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__30_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__32 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__32_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__33 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__33_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__31_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__33_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__34 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__34_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__35 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__35_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ToJson"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__36 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__36_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__37;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__36_value),LEAN_SCALAR_PTR_LITERAL(90, 244, 120, 131, 70, 154, 113, 6)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__38 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__38_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__39_value_aux_0),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__36_value),LEAN_SCALAR_PTR_LITERAL(59, 61, 164, 230, 181, 158, 5, 186)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__39 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__39_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__40 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__40_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__39_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__41 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__41_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__41_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__42 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__42_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__40_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__42_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__43 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__43_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__44 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__44_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__44_value),LEAN_SCALAR_PTR_LITERAL(65, 79, 35, 19, 21, 38, 89, 10)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "variable"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__46 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__46_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__46_value),LEAN_SCALAR_PTR_LITERAL(250, 93, 226, 106, 76, 14, 69, 165)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__48 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__48_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__48_value),LEAN_SCALAR_PTR_LITERAL(37, 156, 84, 218, 244, 57, 142, 153)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__50 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__50_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__50_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__53_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__53_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__53_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__52_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__53 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__53_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__54;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 110, 25, 5, 88, 138, 0, 41)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__55 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__55_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__56 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__56_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__57 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__57_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__56_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__57_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__58 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__58_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__69_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__59 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__59_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__66_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__59_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__60 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__60_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__64_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__60_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__61 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__61_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__62_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__61_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__62 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__62_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__60_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__62_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__63 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__63_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58_value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__63_value)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__64 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__64_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__65 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__65_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__66_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__66_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__66_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__65_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__66 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__66_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__67 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__67_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__68 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__68_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__68_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__70 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__70_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__71_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__71_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__71_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__71_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__71_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__70_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__71 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__71_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__72 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__72_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__73 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__73_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__74_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__74_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__74_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__74_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__73_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__74 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__74_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__75 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__75_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__75_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__76 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__76_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "enc"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__77 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__77_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__78_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__78;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__77_value),LEAN_SCALAR_PTR_LITERAL(127, 112, 184, 188, 166, 208, 172, 147)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__79 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__79_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__80 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__80_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__80_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__81 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__81_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dec"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__82 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__82_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__83_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__83;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__82_value),LEAN_SCALAR_PTR_LITERAL(133, 11, 154, 178, 201, 214, 183, 192)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__84 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__84_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__85 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__85_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__86_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__86_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__86_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__86_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__86_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__86_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__85_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__86 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__86_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__87 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__87_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__88 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__88_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__89 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__89_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90_value_aux_1),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__88_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__89_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "whereDecls"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__91 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__91_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__91_value),LEAN_SCALAR_PTR_LITERAL(51, 156, 180, 247, 37, 30, 126, 62)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letRecDecl"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__93 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__93_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__93_value),LEAN_SCALAR_PTR_LITERAL(202, 48, 93, 231, 206, 172, 150, 190)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__95 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__95_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__95_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__97 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__97_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__97_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__99 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__99_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__99_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "termReturn"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__101 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__101_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__102_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__102_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__102_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__102_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__102_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__102_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__101_value),LEAN_SCALAR_PTR_LITERAL(199, 245, 184, 22, 191, 152, 219, 48)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__102 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__102_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "return"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__103 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__103_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toJson"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__104 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__104_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__105_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__105;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__104_value),LEAN_SCALAR_PTR_LITERAL(112, 200, 227, 76, 90, 242, 6, 135)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__106 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__106_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__107_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__107_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__107_value_aux_0),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__36_value),LEAN_SCALAR_PTR_LITERAL(59, 61, 164, 230, 181, 158, 5, 186)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__107_value_aux_1),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__104_value),LEAN_SCALAR_PTR_LITERAL(240, 112, 235, 135, 88, 35, 83, 81)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__107 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__107_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__107_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__108 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__108_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__108_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__109 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__109_value;
lean_object* l_Lean_mkAtom(lean_object*);
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__110_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__110;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "j"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__111 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__111_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__112_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__112;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__111_value),LEAN_SCALAR_PTR_LITERAL(71, 110, 153, 29, 75, 133, 244, 52)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__113 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__113_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__114 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__114_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__114_value),LEAN_SCALAR_PTR_LITERAL(181, 206, 135, 90, 45, 65, 187, 80)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__116 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__116_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__116_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__118 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__118_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__118_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doLetArrow"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__120 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__120_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__121_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__121_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__121_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__121_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__121_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__121_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__120_value),LEAN_SCALAR_PTR_LITERAL(155, 105, 77, 168, 26, 188, 17, 34)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__121 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__121_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__122 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__122_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIdDecl"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__123 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__123_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__123_value),LEAN_SCALAR_PTR_LITERAL(41, 95, 84, 160, 28, 70, 78, 179)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__125 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__125_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__125_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fromJson\?"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__127 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__127_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__127_value),LEAN_SCALAR_PTR_LITERAL(3, 54, 193, 250, 66, 68, 188, 53)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__129 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__129_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__130_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__130_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__130_value_aux_0),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__27_value),LEAN_SCALAR_PTR_LITERAL(56, 129, 161, 88, 112, 64, 72, 138)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__130_value_aux_1),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__127_value),LEAN_SCALAR_PTR_LITERAL(196, 88, 105, 59, 236, 221, 213, 61)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__130 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__130_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__130_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__131 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__131_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__131_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__132 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__132_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doReturn"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__133 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__133_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__133_value),LEAN_SCALAR_PTR_LITERAL(210, 201, 30, 244, 146, 7, 54, 39)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "for structure "};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__135 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__135_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__136_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__136;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " with params "};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__137 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__137_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__138_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__138;
lean_object* l_Lean_getStructureFieldsFlattened(lean_object*, lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_termParser(lean_object*);
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__0;
lean_object* l_Lean_Parser_Term_matchAlt(lean_object*);
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm;
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___closed__0 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__1_value;
static const lean_closure_object l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___lam__0___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__1_value)} };
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__2_value;
lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__1_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__2_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__3_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__4_value;
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__5 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__5_value;
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__6 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__6_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__13___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__3;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg___closed__2;
extern lean_object* l_Lean_Elab_pp_macroStack;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__6_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__7;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ctor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 61, 118, 113, 180, 158, 239, 32)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dotIdent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(173, 139, 76, 218, 89, 59, 213, 196)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__9_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__9_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "constructor name not a string: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__11;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___closed__0_value;
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__13_spec__17(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__13_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__13(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__13___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "inductive"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__0 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 178, 72, 69, 244, 64, 6, 60)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__1 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__1_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "partial"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__2 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__2_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 175, 198, 167, 172, 79, 14, 207)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__3 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__3_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__4;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "have"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__5 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__5_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__5_value),LEAN_SCALAR_PTR_LITERAL(55, 91, 239, 116, 115, 0, 62, 115)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__6 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__6_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__7 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__7_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__8_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__7_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__8 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__8_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "inst"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__9 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__9_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__10;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__9_value),LEAN_SCALAR_PTR_LITERAL(170, 188, 240, 205, 110, 63, 170, 91)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__11 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__11_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__12 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__12_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__13_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__13_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__12_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__13 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__13_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__14 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__14_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__15_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__15_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__15_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__14_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__15 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__15_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__16 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__16_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__17 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__17_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__18_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__18_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__17_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__18 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__18_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doHave"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__19 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__19_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__20_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__20_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__19_value),LEAN_SCALAR_PTR_LITERAL(103, 74, 100, 51, 242, 214, 142, 115)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__20 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__20_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pkt"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__21 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__21_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__22;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__21_value),LEAN_SCALAR_PTR_LITERAL(182, 192, 230, 127, 128, 175, 248, 240)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__23 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__23_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_<|_"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__24 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__24_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__24_value),LEAN_SCALAR_PTR_LITERAL(152, 38, 96, 140, 215, 46, 31, 82)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__25 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__25_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__26 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__26_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__27;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__26_value),LEAN_SCALAR_PTR_LITERAL(223, 78, 141, 85, 50, 255, 216, 83)}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__28 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__28_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__28_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__29 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__29_value;
static const lean_ctor_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__30 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__30_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "<|"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__31 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__31_value;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "for inductive "};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__32 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__32_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__33;
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instBinder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 219, 89, 171, 221, 95, 22, 227)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__58_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__3_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__4_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__5;
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__1;
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "indexed inductive families are not supported"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__0 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__0_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__1;
static const lean_string_object l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "mutually inductive types are not supported"};
static const lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__2 = (const lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__2_value;
static lean_once_cell_t l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_RpcEncodable_initFn___closed__0_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_RpcEncodable_initFn___closed__0_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__0_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Server_RpcEncodable_initFn___closed__1_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lean_Server_RpcEncodable_initFn___closed__1_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__1_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Server_RpcEncodable_initFn___closed__2_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__1_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_object* l_Lean_Server_RpcEncodable_initFn___closed__2_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__2_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Server_RpcEncodable_initFn___closed__3_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__2_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 192, 180, 137, 118, 34, 3, 132)}};
static const lean_object* l_Lean_Server_RpcEncodable_initFn___closed__3_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__3_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Server_RpcEncodable_initFn___closed__4_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l_Lean_Server_RpcEncodable_initFn___closed__4_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__4_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Server_RpcEncodable_initFn___closed__5_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__3_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__4_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(20, 224, 96, 44, 73, 125, 110, 125)}};
static const lean_object* l_Lean_Server_RpcEncodable_initFn___closed__5_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__5_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Server_RpcEncodable_initFn___closed__6_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l_Lean_Server_RpcEncodable_initFn___closed__6_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__6_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Server_RpcEncodable_initFn___closed__7_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__5_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__6_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(61, 147, 200, 62, 97, 85, 87, 110)}};
static const lean_object* l_Lean_Server_RpcEncodable_initFn___closed__7_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__7_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Server_RpcEncodable_initFn___closed__8_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__7_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 142, 237, 108, 78, 65, 25, 27)}};
static const lean_object* l_Lean_Server_RpcEncodable_initFn___closed__8_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__8_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Server_RpcEncodable_initFn___closed__9_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__8_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(213, 60, 137, 124, 196, 100, 251, 16)}};
static const lean_object* l_Lean_Server_RpcEncodable_initFn___closed__9_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__9_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Server_RpcEncodable_initFn___closed__10_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rpc"};
static const lean_object* l_Lean_Server_RpcEncodable_initFn___closed__10_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__10_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Server_RpcEncodable_initFn___closed__11_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__9_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__10_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 249, 241, 171, 115, 19, 180, 46)}};
static const lean_object* l_Lean_Server_RpcEncodable_initFn___closed__11_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__11_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Server_RpcEncodable_initFn___closed__12_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__11_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(228, 195, 253, 95, 10, 231, 180, 41)}};
static const lean_object* l_Lean_Server_RpcEncodable_initFn___closed__12_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__12_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Server_RpcEncodable_initFn___closed__13_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__12_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)(((size_t)(198155338) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(172, 252, 211, 227, 209, 184, 14, 138)}};
static const lean_object* l_Lean_Server_RpcEncodable_initFn___closed__13_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__13_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Server_RpcEncodable_initFn___closed__14_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l_Lean_Server_RpcEncodable_initFn___closed__14_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__14_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Server_RpcEncodable_initFn___closed__15_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__13_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__14_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 246, 189, 3, 195, 99, 85, 4)}};
static const lean_object* l_Lean_Server_RpcEncodable_initFn___closed__15_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__15_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Server_RpcEncodable_initFn___closed__16_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l_Lean_Server_RpcEncodable_initFn___closed__16_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__16_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Server_RpcEncodable_initFn___closed__17_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__15_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__16_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(3, 114, 249, 33, 217, 11, 151, 145)}};
static const lean_object* l_Lean_Server_RpcEncodable_initFn___closed__17_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__17_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Server_RpcEncodable_initFn___closed__18_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__17_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(198, 178, 219, 247, 243, 144, 233, 214)}};
static const lean_object* l_Lean_Server_RpcEncodable_initFn___closed__18_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Server_RpcEncodable_initFn___closed__18_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2__value;
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RpcEncodable_initFn_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Server_RpcEncodable_initFn_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_Server_RpcEncodable_isOptField___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Server_RpcEncodable_isOptField___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Server_RpcEncodable_isOptField(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
x_4 = ((lean_object*)(l_Lean_Server_RpcEncodable_isOptField___closed__0));
x_5 = lean_string_utf8_byte_size(x_3);
x_6 = lean_obj_once(&l_Lean_Server_RpcEncodable_isOptField___closed__1, &l_Lean_Server_RpcEncodable_isOptField___closed__1_once, _init_l_Lean_Server_RpcEncodable_isOptField___closed__1);
x_7 = lean_nat_dec_le(x_6, x_5);
if (x_7 == 0)
{
lean_dec_ref(x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_sub(x_5, x_6);
x_10 = lean_string_memcmp(x_3, x_4, x_9, x_8, x_6);
lean_dec(x_9);
lean_dec_ref(x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RpcEncodable_isOptField___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Server_RpcEncodable_isOptField(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg(x_1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7_spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__0(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_53; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7_spec__7(x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
x_11 = x_9;
x_12 = x_53;
goto block_52;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_51; 
x_13 = lean_st_ref_take(x_6);
x_14 = lean_ctor_get(x_13, 4);
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 5);
x_20 = lean_ctor_get(x_13, 6);
x_21 = lean_ctor_get(x_13, 7);
x_22 = lean_ctor_get(x_13, 8);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
x_23 = x_13;
x_24 = x_51;
goto block_50;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_14);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_51;
goto block_50;
}
block_50:
{
uint64_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_49; 
x_25 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_26 = lean_ctor_get(x_14, 0);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
x_27 = x_14;
x_28 = x_49;
goto block_48;
}
else
{
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = x_49;
goto block_48;
}
block_48:
{
double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__0);
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__2));
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_10);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_26, x_35);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_36);
x_37 = x_27;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set_uint64(x_47, sizeof(void*)*1, x_25);
x_37 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_38; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_37);
x_38 = x_23;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_16);
lean_ctor_set(x_45, 2, x_17);
lean_ctor_set(x_45, 3, x_18);
lean_ctor_set(x_45, 4, x_37);
lean_ctor_set(x_45, 5, x_19);
lean_ctor_set(x_45, 6, x_20);
lean_ctor_set(x_45, 7, x_21);
lean_ctor_set(x_45, 8, x_22);
x_38 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_st_ref_set(x_6, x_38);
x_40 = lean_box(0);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_40);
x_41 = x_11;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_37; 
x_8 = lean_array_uget(x_6, x_5);
x_9 = lean_ctor_get(x_8, 0);
x_10 = lean_ctor_get(x_8, 1);
x_37 = !lean_is_exclusive(x_8);
if (x_37 == 0)
{
x_11 = x_8;
x_12 = x_37;
goto block_36;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
x_14 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6));
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_6, x_5, x_15);
x_17 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__8));
x_18 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__9));
lean_inc(x_1);
if (x_12 == 0)
{
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_18);
lean_ctor_set(x_11, 0, x_1);
x_19 = x_11;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_18);
x_19 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
lean_inc(x_1);
x_20 = l_Lean_Syntax_node1(x_1, x_13, x_9);
x_21 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12));
x_22 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__13));
lean_inc(x_1);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
lean_inc(x_1);
x_24 = l_Lean_Syntax_node2(x_1, x_21, x_23, x_10);
lean_inc(x_1);
x_25 = l_Lean_Syntax_node1(x_1, x_13, x_24);
lean_inc(x_2);
lean_inc(x_1);
x_26 = l_Lean_Syntax_node2(x_1, x_14, x_2, x_25);
x_27 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__14));
lean_inc(x_1);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_29 = l_Lean_Syntax_node6(x_1, x_17, x_3, x_19, x_20, x_26, x_2, x_28);
x_30 = 1;
x_31 = lean_usize_add(x_5, x_30);
x_32 = lean_array_uset(x_16, x_5, x_29);
x_5 = x_31;
x_6 = x_32;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
x_6 = x_1;
x_7 = x_14;
goto block_13;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_MessageData_ofExpr(x_4);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_8);
x_9 = x_6;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_2);
x_9 = x_12;
goto block_11;
}
block_11:
{
x_1 = x_5;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_4);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget_borrowed(x_3, x_2);
lean_inc_ref(x_4);
x_11 = l_Lean_Meta_getFVarLocalDecl___redArg(x_10, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = l_Lean_LocalDecl_userName(x_12);
lean_dec(x_12);
x_16 = lean_mk_syntax_ident(x_15);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_14, x_2, x_16);
x_2 = x_18;
x_3 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_21 = lean_ctor_get(x_11, 0);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
x_22 = x_11;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___redArg(x_8, x_9, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = l_Lean_SourceInfo_fromRef(x_9, x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__1));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__19));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__29(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__28));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__35));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__42(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__41));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg___closed__1));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__77(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__76));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_3, x_2);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec_ref(x_9);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_262; 
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_4, 0);
x_262 = !lean_is_exclusive(x_4);
if (x_262 == 0)
{
lean_object* x_263; 
x_263 = lean_ctor_get(x_4, 1);
lean_dec(x_263);
x_23 = x_4;
x_24 = x_262;
goto block_261;
}
else
{
lean_inc(x_22);
lean_dec(x_4);
x_23 = lean_box(0);
x_24 = x_262;
goto block_261;
}
block_261:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_259; 
x_25 = lean_ctor_get(x_20, 0);
x_259 = !lean_is_exclusive(x_20);
if (x_259 == 0)
{
lean_object* x_260; 
x_260 = lean_ctor_get(x_20, 1);
lean_dec(x_260);
x_26 = x_20;
x_27 = x_259;
goto block_258;
}
else
{
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = x_259;
goto block_258;
}
block_258:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_257; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
x_257 = !lean_is_exclusive(x_21);
if (x_257 == 0)
{
x_30 = x_21;
x_31 = x_257;
goto block_256;
}
else
{
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_box(0);
x_31 = x_257;
goto block_256;
}
block_256:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_array_uget_borrowed(x_1, x_3);
lean_inc(x_32);
x_33 = lean_mk_syntax_ident(x_32);
lean_inc(x_33);
x_34 = lean_array_push(x_28, x_33);
lean_inc(x_32);
x_35 = l_Lean_Server_RpcEncodable_isOptField(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_9, 5);
x_37 = lean_ctor_get(x_9, 10);
x_38 = lean_ctor_get(x_9, 11);
x_39 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__2);
x_40 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__0(x_35, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3));
x_43 = lean_box(0);
x_44 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__7));
x_45 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__9));
x_46 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
x_47 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10);
lean_inc(x_41);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_47);
lean_inc_ref(x_48);
lean_inc(x_33);
lean_inc(x_41);
x_49 = l_Lean_Syntax_node2(x_41, x_45, x_33, x_48);
x_50 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__12));
x_51 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13));
lean_inc(x_41);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_51);
x_53 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15));
x_54 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16));
lean_inc(x_41);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_41);
lean_ctor_set(x_55, 1, x_54);
x_56 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18));
x_57 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20);
x_58 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21));
lean_inc(x_38);
lean_inc(x_37);
x_59 = l_Lean_addMacroScope(x_37, x_58, x_38);
x_60 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__25));
lean_inc(x_41);
x_61 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_57);
lean_ctor_set(x_61, 2, x_59);
lean_ctor_set(x_61, 3, x_60);
x_62 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__27));
x_63 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__29, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__29);
x_64 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30));
lean_inc(x_38);
lean_inc(x_37);
x_65 = l_Lean_addMacroScope(x_37, x_64, x_38);
lean_inc(x_65);
lean_inc(x_41);
x_66 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_66, 0, x_41);
lean_ctor_set(x_66, 1, x_63);
lean_ctor_set(x_66, 2, x_65);
lean_ctor_set(x_66, 3, x_43);
x_67 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__31));
lean_inc(x_41);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_41);
lean_ctor_set(x_68, 1, x_67);
lean_inc(x_33);
lean_inc(x_41);
x_69 = l_Lean_Syntax_node3(x_41, x_62, x_66, x_68, x_33);
lean_inc(x_41);
x_70 = l_Lean_Syntax_node1(x_41, x_46, x_69);
lean_inc(x_41);
x_71 = l_Lean_Syntax_node2(x_41, x_56, x_61, x_70);
lean_inc(x_41);
x_72 = l_Lean_Syntax_node2(x_41, x_53, x_55, x_71);
lean_inc_ref(x_48);
lean_inc(x_41);
x_73 = l_Lean_Syntax_node3(x_41, x_50, x_52, x_48, x_72);
lean_inc_ref(x_48);
lean_inc(x_41);
x_74 = l_Lean_Syntax_node3(x_41, x_46, x_48, x_48, x_73);
x_75 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__0(x_35, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
x_77 = l_Lean_SourceInfo_fromRef(x_36, x_35);
lean_inc(x_38);
lean_inc(x_37);
x_78 = l_Lean_addMacroScope(x_37, x_42, x_38);
x_79 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__34));
x_80 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_39);
lean_ctor_set(x_80, 2, x_78);
lean_ctor_set(x_80, 3, x_79);
x_81 = lean_array_push(x_29, x_80);
x_82 = l_Lean_Syntax_node2(x_41, x_44, x_49, x_74);
x_83 = lean_array_push(x_25, x_82);
lean_inc(x_76);
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_76);
lean_ctor_set(x_84, 1, x_46);
lean_ctor_set(x_84, 2, x_47);
lean_inc_ref(x_84);
lean_inc(x_33);
lean_inc(x_76);
x_85 = l_Lean_Syntax_node2(x_76, x_45, x_33, x_84);
lean_inc(x_76);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_76);
lean_ctor_set(x_86, 1, x_51);
lean_inc(x_76);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_76);
lean_ctor_set(x_87, 1, x_54);
x_88 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36);
x_89 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37));
lean_inc(x_38);
lean_inc(x_37);
x_90 = l_Lean_addMacroScope(x_37, x_89, x_38);
x_91 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__40));
lean_inc(x_76);
x_92 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_92, 0, x_76);
lean_ctor_set(x_92, 1, x_88);
lean_ctor_set(x_92, 2, x_90);
lean_ctor_set(x_92, 3, x_91);
lean_inc(x_76);
x_93 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_93, 0, x_76);
lean_ctor_set(x_93, 1, x_63);
lean_ctor_set(x_93, 2, x_65);
lean_ctor_set(x_93, 3, x_43);
lean_inc(x_76);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_76);
lean_ctor_set(x_94, 1, x_67);
lean_inc(x_76);
x_95 = l_Lean_Syntax_node3(x_76, x_62, x_93, x_94, x_33);
lean_inc(x_76);
x_96 = l_Lean_Syntax_node1(x_76, x_46, x_95);
lean_inc(x_76);
x_97 = l_Lean_Syntax_node2(x_76, x_56, x_92, x_96);
lean_inc(x_76);
x_98 = l_Lean_Syntax_node2(x_76, x_53, x_87, x_97);
lean_inc_ref(x_84);
lean_inc(x_76);
x_99 = l_Lean_Syntax_node3(x_76, x_50, x_86, x_84, x_98);
lean_inc_ref(x_84);
lean_inc(x_76);
x_100 = l_Lean_Syntax_node3(x_76, x_46, x_84, x_84, x_99);
x_101 = l_Lean_Syntax_node2(x_76, x_44, x_85, x_100);
x_102 = lean_array_push(x_22, x_101);
if (x_31 == 0)
{
lean_ctor_set(x_30, 1, x_81);
lean_ctor_set(x_30, 0, x_34);
x_103 = x_30;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_34);
lean_ctor_set(x_111, 1, x_81);
x_103 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_104; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 1, x_103);
lean_ctor_set(x_26, 0, x_83);
x_104 = x_26;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_83);
lean_ctor_set(x_109, 1, x_103);
x_104 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_105; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 1, x_104);
lean_ctor_set(x_23, 0, x_102);
x_105 = x_23;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_102);
lean_ctor_set(x_107, 1, x_104);
x_105 = x_107;
goto block_106;
}
block_106:
{
x_12 = x_105;
x_13 = lean_box(0);
goto block_17;
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_119; 
lean_dec(x_74);
lean_dec(x_65);
lean_dec(x_49);
lean_dec(x_41);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_del_object(x_30);
lean_dec(x_29);
lean_del_object(x_26);
lean_dec(x_25);
lean_del_object(x_23);
lean_dec(x_22);
lean_dec_ref(x_9);
x_112 = lean_ctor_get(x_75, 0);
x_119 = !lean_is_exclusive(x_75);
if (x_119 == 0)
{
x_113 = x_75;
x_114 = x_119;
goto block_118;
}
else
{
lean_inc(x_112);
lean_dec(x_75);
x_113 = lean_box(0);
x_114 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_115; 
if (x_114 == 0)
{
x_115 = x_113;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_112);
x_115 = x_117;
goto block_116;
}
block_116:
{
return x_115;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_127; 
lean_dec_ref(x_34);
lean_dec(x_33);
lean_del_object(x_30);
lean_dec(x_29);
lean_del_object(x_26);
lean_dec(x_25);
lean_del_object(x_23);
lean_dec(x_22);
lean_dec_ref(x_9);
x_120 = lean_ctor_get(x_40, 0);
x_127 = !lean_is_exclusive(x_40);
if (x_127 == 0)
{
x_121 = x_40;
x_122 = x_127;
goto block_126;
}
else
{
lean_inc(x_120);
lean_dec(x_40);
x_121 = lean_box(0);
x_122 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_123; 
if (x_122 == 0)
{
x_123 = x_121;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_120);
x_123 = x_125;
goto block_124;
}
block_124:
{
return x_123;
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_128 = lean_ctor_get(x_9, 5);
x_129 = lean_ctor_get(x_9, 10);
x_130 = lean_ctor_get(x_9, 11);
x_131 = 0;
x_132 = l_Lean_SourceInfo_fromRef(x_128, x_131);
x_133 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18));
x_134 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__42, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__42_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__42);
x_135 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__43));
lean_inc(x_130);
lean_inc(x_129);
x_136 = l_Lean_addMacroScope(x_129, x_135, x_130);
x_137 = lean_box(0);
x_138 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__48));
lean_inc(x_132);
x_139 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_139, 0, x_132);
lean_ctor_set(x_139, 1, x_134);
lean_ctor_set(x_139, 2, x_136);
lean_ctor_set(x_139, 3, x_138);
x_140 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__2);
x_141 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3));
x_142 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__1(x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
lean_inc(x_130);
lean_inc(x_129);
x_144 = l_Lean_addMacroScope(x_129, x_141, x_130);
x_145 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__34));
lean_inc(x_132);
x_146 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_146, 0, x_132);
lean_ctor_set(x_146, 1, x_140);
lean_ctor_set(x_146, 2, x_144);
lean_ctor_set(x_146, 3, x_145);
x_147 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
lean_inc(x_132);
x_148 = l_Lean_Syntax_node1(x_132, x_147, x_146);
x_149 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__7));
x_150 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__9));
x_151 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10);
lean_inc(x_143);
x_152 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_152, 0, x_143);
lean_ctor_set(x_152, 1, x_147);
lean_ctor_set(x_152, 2, x_151);
lean_inc_ref(x_152);
lean_inc(x_33);
lean_inc(x_143);
x_153 = l_Lean_Syntax_node2(x_143, x_150, x_33, x_152);
x_154 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__12));
x_155 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13));
lean_inc(x_143);
x_156 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_156, 0, x_143);
lean_ctor_set(x_156, 1, x_155);
x_157 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15));
x_158 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16));
lean_inc(x_143);
x_159 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_159, 0, x_143);
lean_ctor_set(x_159, 1, x_158);
x_160 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__27));
x_161 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51));
x_162 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53));
x_163 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__9));
lean_inc(x_143);
x_164 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_164, 0, x_143);
lean_ctor_set(x_164, 1, x_163);
x_165 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55));
x_166 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56);
x_167 = lean_box(0);
lean_inc(x_130);
lean_inc(x_129);
x_168 = l_Lean_addMacroScope(x_129, x_167, x_130);
x_169 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__75));
lean_inc(x_168);
lean_inc(x_143);
x_170 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_170, 0, x_143);
lean_ctor_set(x_170, 1, x_166);
lean_ctor_set(x_170, 2, x_168);
lean_ctor_set(x_170, 3, x_169);
lean_inc(x_143);
x_171 = l_Lean_Syntax_node1(x_143, x_165, x_170);
lean_inc(x_143);
x_172 = l_Lean_Syntax_node2(x_143, x_162, x_164, x_171);
x_173 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__29, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__29);
x_174 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30));
lean_inc(x_130);
lean_inc(x_129);
x_175 = l_Lean_addMacroScope(x_129, x_174, x_130);
lean_inc(x_175);
lean_inc(x_143);
x_176 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_176, 0, x_143);
lean_ctor_set(x_176, 1, x_173);
lean_ctor_set(x_176, 2, x_175);
lean_ctor_set(x_176, 3, x_137);
x_177 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__31));
lean_inc(x_143);
x_178 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_178, 0, x_143);
lean_ctor_set(x_178, 1, x_177);
lean_inc(x_33);
lean_inc_ref(x_178);
lean_inc(x_143);
x_179 = l_Lean_Syntax_node3(x_143, x_160, x_176, x_178, x_33);
x_180 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__14));
lean_inc(x_143);
x_181 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_181, 0, x_143);
lean_ctor_set(x_181, 1, x_180);
lean_inc(x_143);
x_182 = l_Lean_Syntax_node3(x_143, x_161, x_172, x_179, x_181);
x_183 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__77, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__77_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__77);
x_184 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__78));
lean_inc(x_130);
lean_inc(x_129);
x_185 = l_Lean_addMacroScope(x_129, x_184, x_130);
lean_inc(x_185);
lean_inc(x_143);
x_186 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_186, 0, x_143);
lean_ctor_set(x_186, 1, x_183);
lean_ctor_set(x_186, 2, x_185);
lean_ctor_set(x_186, 3, x_137);
lean_inc(x_143);
x_187 = l_Lean_Syntax_node3(x_143, x_160, x_182, x_178, x_186);
x_188 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20);
x_189 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21));
lean_inc(x_130);
lean_inc(x_129);
x_190 = l_Lean_addMacroScope(x_129, x_189, x_130);
x_191 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__25));
lean_inc(x_143);
x_192 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_192, 0, x_143);
lean_ctor_set(x_192, 1, x_188);
lean_ctor_set(x_192, 2, x_190);
lean_ctor_set(x_192, 3, x_191);
lean_inc(x_143);
x_193 = l_Lean_Syntax_node1(x_143, x_147, x_192);
lean_inc(x_143);
x_194 = l_Lean_Syntax_node2(x_143, x_133, x_187, x_193);
lean_inc(x_143);
x_195 = l_Lean_Syntax_node2(x_143, x_157, x_159, x_194);
lean_inc_ref(x_152);
lean_inc(x_143);
x_196 = l_Lean_Syntax_node3(x_143, x_154, x_156, x_152, x_195);
lean_inc_ref(x_152);
lean_inc(x_143);
x_197 = l_Lean_Syntax_node3(x_143, x_147, x_152, x_152, x_196);
x_198 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___lam__1(x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
lean_dec_ref(x_198);
x_200 = l_Lean_Syntax_node2(x_132, x_133, x_139, x_148);
x_201 = lean_array_push(x_29, x_200);
x_202 = l_Lean_Syntax_node2(x_143, x_149, x_153, x_197);
x_203 = lean_array_push(x_25, x_202);
lean_inc(x_199);
x_204 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_204, 0, x_199);
lean_ctor_set(x_204, 1, x_147);
lean_ctor_set(x_204, 2, x_151);
lean_inc_ref(x_204);
lean_inc(x_33);
lean_inc(x_199);
x_205 = l_Lean_Syntax_node2(x_199, x_150, x_33, x_204);
lean_inc(x_199);
x_206 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_206, 0, x_199);
lean_ctor_set(x_206, 1, x_155);
lean_inc(x_199);
x_207 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_207, 0, x_199);
lean_ctor_set(x_207, 1, x_158);
lean_inc(x_199);
x_208 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_208, 0, x_199);
lean_ctor_set(x_208, 1, x_163);
lean_inc(x_199);
x_209 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_209, 0, x_199);
lean_ctor_set(x_209, 1, x_166);
lean_ctor_set(x_209, 2, x_168);
lean_ctor_set(x_209, 3, x_169);
lean_inc(x_199);
x_210 = l_Lean_Syntax_node1(x_199, x_165, x_209);
lean_inc(x_199);
x_211 = l_Lean_Syntax_node2(x_199, x_162, x_208, x_210);
lean_inc(x_199);
x_212 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_212, 0, x_199);
lean_ctor_set(x_212, 1, x_173);
lean_ctor_set(x_212, 2, x_175);
lean_ctor_set(x_212, 3, x_137);
lean_inc(x_199);
x_213 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_213, 0, x_199);
lean_ctor_set(x_213, 1, x_177);
lean_inc_ref(x_213);
lean_inc(x_199);
x_214 = l_Lean_Syntax_node3(x_199, x_160, x_212, x_213, x_33);
lean_inc(x_199);
x_215 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_215, 0, x_199);
lean_ctor_set(x_215, 1, x_180);
lean_inc(x_199);
x_216 = l_Lean_Syntax_node3(x_199, x_161, x_211, x_214, x_215);
lean_inc(x_199);
x_217 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_217, 0, x_199);
lean_ctor_set(x_217, 1, x_183);
lean_ctor_set(x_217, 2, x_185);
lean_ctor_set(x_217, 3, x_137);
lean_inc(x_199);
x_218 = l_Lean_Syntax_node3(x_199, x_160, x_216, x_213, x_217);
x_219 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36);
x_220 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37));
lean_inc(x_130);
lean_inc(x_129);
x_221 = l_Lean_addMacroScope(x_129, x_220, x_130);
x_222 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__40));
lean_inc(x_199);
x_223 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_223, 0, x_199);
lean_ctor_set(x_223, 1, x_219);
lean_ctor_set(x_223, 2, x_221);
lean_ctor_set(x_223, 3, x_222);
lean_inc(x_199);
x_224 = l_Lean_Syntax_node1(x_199, x_147, x_223);
lean_inc(x_199);
x_225 = l_Lean_Syntax_node2(x_199, x_133, x_218, x_224);
lean_inc(x_199);
x_226 = l_Lean_Syntax_node2(x_199, x_157, x_207, x_225);
lean_inc_ref(x_204);
lean_inc(x_199);
x_227 = l_Lean_Syntax_node3(x_199, x_154, x_206, x_204, x_226);
lean_inc_ref(x_204);
lean_inc(x_199);
x_228 = l_Lean_Syntax_node3(x_199, x_147, x_204, x_204, x_227);
x_229 = l_Lean_Syntax_node2(x_199, x_149, x_205, x_228);
x_230 = lean_array_push(x_22, x_229);
if (x_31 == 0)
{
lean_ctor_set(x_30, 1, x_201);
lean_ctor_set(x_30, 0, x_34);
x_231 = x_30;
goto block_238;
}
else
{
lean_object* x_239; 
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_34);
lean_ctor_set(x_239, 1, x_201);
x_231 = x_239;
goto block_238;
}
block_238:
{
lean_object* x_232; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 1, x_231);
lean_ctor_set(x_26, 0, x_203);
x_232 = x_26;
goto block_236;
}
else
{
lean_object* x_237; 
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_203);
lean_ctor_set(x_237, 1, x_231);
x_232 = x_237;
goto block_236;
}
block_236:
{
lean_object* x_233; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 1, x_232);
lean_ctor_set(x_23, 0, x_230);
x_233 = x_23;
goto block_234;
}
else
{
lean_object* x_235; 
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_230);
lean_ctor_set(x_235, 1, x_232);
x_233 = x_235;
goto block_234;
}
block_234:
{
x_12 = x_233;
x_13 = lean_box(0);
goto block_17;
}
}
}
}
else
{
lean_object* x_240; lean_object* x_241; uint8_t x_242; uint8_t x_247; 
lean_dec(x_197);
lean_dec(x_185);
lean_dec(x_175);
lean_dec(x_168);
lean_dec(x_153);
lean_dec(x_148);
lean_dec(x_143);
lean_dec_ref(x_139);
lean_dec(x_132);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_del_object(x_30);
lean_dec(x_29);
lean_del_object(x_26);
lean_dec(x_25);
lean_del_object(x_23);
lean_dec(x_22);
lean_dec_ref(x_9);
x_240 = lean_ctor_get(x_198, 0);
x_247 = !lean_is_exclusive(x_198);
if (x_247 == 0)
{
x_241 = x_198;
x_242 = x_247;
goto block_246;
}
else
{
lean_inc(x_240);
lean_dec(x_198);
x_241 = lean_box(0);
x_242 = x_247;
goto block_246;
}
block_246:
{
lean_object* x_243; 
if (x_242 == 0)
{
x_243 = x_241;
goto block_244;
}
else
{
lean_object* x_245; 
x_245 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_245, 0, x_240);
x_243 = x_245;
goto block_244;
}
block_244:
{
return x_243;
}
}
}
}
else
{
lean_object* x_248; lean_object* x_249; uint8_t x_250; uint8_t x_255; 
lean_dec_ref(x_139);
lean_dec(x_132);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_del_object(x_30);
lean_dec(x_29);
lean_del_object(x_26);
lean_dec(x_25);
lean_del_object(x_23);
lean_dec(x_22);
lean_dec_ref(x_9);
x_248 = lean_ctor_get(x_142, 0);
x_255 = !lean_is_exclusive(x_142);
if (x_255 == 0)
{
x_249 = x_142;
x_250 = x_255;
goto block_254;
}
else
{
lean_inc(x_248);
lean_dec(x_142);
x_249 = lean_box(0);
x_250 = x_255;
goto block_254;
}
block_254:
{
lean_object* x_251; 
if (x_250 == 0)
{
x_251 = x_249;
goto block_252;
}
else
{
lean_object* x_253; 
x_253 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_253, 0, x_248);
x_251 = x_253;
goto block_252;
}
block_252:
{
return x_251;
}
}
}
}
}
}
}
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__2));
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__3, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__3_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__3);
x_2 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__2));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__4, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__4_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__4);
x_2 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__2));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__16));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__28(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__27));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__37(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__36));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__54(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__78(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__77));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__83(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__82));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__105(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__104));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__110(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__35));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__112(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__111));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__127));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__136(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__135));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__138(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__137));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_353; 
x_11 = lean_st_ref_get(x_9);
x_12 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__1));
x_13 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg(x_12, x_8);
x_14 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_14);
lean_dec_ref(x_1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_14, 0);
x_353 = !lean_is_exclusive(x_14);
if (x_353 == 0)
{
lean_object* x_354; lean_object* x_355; 
x_354 = lean_ctor_get(x_14, 2);
lean_dec(x_354);
x_355 = lean_ctor_get(x_14, 1);
lean_dec(x_355);
x_18 = x_14;
x_19 = x_353;
goto block_352;
}
else
{
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = x_353;
goto block_352;
}
block_352:
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_332; 
x_20 = 0;
lean_inc(x_17);
x_21 = l_Lean_getStructureFieldsFlattened(x_16, x_17, x_20);
x_332 = lean_unbox(x_15);
lean_dec(x_15);
if (x_332 == 0)
{
x_22 = x_4;
x_23 = x_5;
x_24 = x_6;
x_25 = x_7;
x_26 = x_8;
x_27 = x_9;
x_28 = lean_box(0);
goto block_331;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_333 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__136, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__136_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__136);
lean_inc(x_17);
x_334 = l_Lean_MessageData_ofName(x_17);
x_335 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
x_336 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__138, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__138_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__138);
x_337 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_336);
lean_inc_ref(x_2);
x_338 = lean_array_to_list(x_2);
x_339 = lean_box(0);
x_340 = l_List_mapTR_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__6(x_338, x_339);
x_341 = l_Lean_MessageData_ofList(x_340);
x_342 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_342, 0, x_337);
lean_ctor_set(x_342, 1, x_341);
x_343 = l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg(x_12, x_342, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_343) == 0)
{
lean_dec_ref(x_343);
x_22 = x_4;
x_23 = x_5;
x_24 = x_6;
x_25 = x_7;
x_26 = x_8;
x_27 = x_9;
x_28 = lean_box(0);
goto block_331;
}
else
{
lean_object* x_344; lean_object* x_345; uint8_t x_346; uint8_t x_351; 
lean_dec_ref(x_21);
lean_del_object(x_18);
lean_dec(x_17);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_344 = lean_ctor_get(x_343, 0);
x_351 = !lean_is_exclusive(x_343);
if (x_351 == 0)
{
x_345 = x_343;
x_346 = x_351;
goto block_350;
}
else
{
lean_inc(x_344);
lean_dec(x_343);
x_345 = lean_box(0);
x_346 = x_351;
goto block_350;
}
block_350:
{
lean_object* x_347; 
if (x_346 == 0)
{
x_347 = x_345;
goto block_348;
}
else
{
lean_object* x_349; 
x_349 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_349, 0, x_344);
x_347 = x_349;
goto block_348;
}
block_348:
{
return x_347;
}
}
}
}
block_331:
{
lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_29 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__5, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__5_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__5);
x_30 = lean_array_size(x_21);
x_31 = 0;
lean_inc_ref(x_26);
x_32 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1(x_21, x_30, x_31, x_29, x_22, x_23, x_24, x_25, x_26, x_27);
lean_dec_ref(x_21);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_321; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 0);
x_321 = !lean_is_exclusive(x_33);
if (x_321 == 0)
{
lean_object* x_322; 
x_322 = lean_ctor_get(x_33, 1);
lean_dec(x_322);
x_37 = x_33;
x_38 = x_321;
goto block_320;
}
else
{
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_box(0);
x_38 = x_321;
goto block_320;
}
block_320:
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_318; 
x_39 = lean_ctor_get(x_34, 0);
x_318 = !lean_is_exclusive(x_34);
if (x_318 == 0)
{
lean_object* x_319; 
x_319 = lean_ctor_get(x_34, 1);
lean_dec(x_319);
x_40 = x_34;
x_41 = x_318;
goto block_317;
}
else
{
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_box(0);
x_41 = x_318;
goto block_317;
}
block_317:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_316; 
x_42 = lean_ctor_get(x_35, 0);
x_43 = lean_ctor_get(x_35, 1);
x_316 = !lean_is_exclusive(x_35);
if (x_316 == 0)
{
x_44 = x_35;
x_45 = x_316;
goto block_315;
}
else
{
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_35);
x_44 = lean_box(0);
x_45 = x_316;
goto block_315;
}
block_315:
{
size_t x_46; lean_object* x_47; 
x_46 = lean_array_size(x_2);
x_47 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___redArg(x_46, x_31, x_2, x_24, x_26, x_27);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_306; 
x_48 = lean_ctor_get(x_47, 0);
x_306 = !lean_is_exclusive(x_47);
if (x_306 == 0)
{
x_49 = x_47;
x_50 = x_306;
goto block_305;
}
else
{
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = x_306;
goto block_305;
}
block_305:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_26, 5);
lean_inc(x_51);
x_52 = lean_ctor_get(x_26, 10);
lean_inc(x_52);
x_53 = lean_ctor_get(x_26, 11);
lean_inc(x_53);
lean_dec_ref(x_26);
x_54 = l_Lean_SourceInfo_fromRef(x_51, x_20);
lean_dec(x_51);
x_55 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
x_56 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7));
x_57 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9));
x_58 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10);
lean_inc(x_54);
if (x_19 == 0)
{
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 2, x_58);
lean_ctor_set(x_18, 1, x_55);
lean_ctor_set(x_18, 0, x_54);
x_59 = x_18;
goto block_303;
}
else
{
lean_object* x_304; 
x_304 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_304, 0, x_54);
lean_ctor_set(x_304, 1, x_55);
lean_ctor_set(x_304, 2, x_58);
x_59 = x_304;
goto block_303;
}
block_303:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_inc_ref_n(x_59, 7);
lean_inc(x_54);
x_60 = l_Lean_Syntax_node7(x_54, x_57, x_59, x_59, x_59, x_59, x_59, x_59, x_59);
x_61 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__10));
x_62 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__11));
x_63 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__13));
lean_inc(x_54);
if (x_45 == 0)
{
lean_ctor_set_tag(x_44, 2);
lean_ctor_set(x_44, 1, x_61);
lean_ctor_set(x_44, 0, x_54);
x_64 = x_44;
goto block_301;
}
else
{
lean_object* x_302; 
x_302 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_302, 0, x_54);
lean_ctor_set(x_302, 1, x_61);
x_64 = x_302;
goto block_301;
}
block_301:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_inc(x_54);
x_65 = l_Lean_Syntax_node1(x_54, x_63, x_64);
x_66 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15));
x_67 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__17, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__17_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__17);
x_68 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__18));
lean_inc(x_53);
lean_inc(x_52);
x_69 = l_Lean_addMacroScope(x_52, x_68, x_53);
x_70 = lean_box(0);
lean_inc(x_54);
x_71 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_71, 0, x_54);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set(x_71, 2, x_69);
lean_ctor_set(x_71, 3, x_70);
lean_inc_ref(x_59);
lean_inc_ref(x_71);
lean_inc(x_54);
x_72 = l_Lean_Syntax_node2(x_54, x_66, x_71, x_59);
x_73 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6));
lean_inc_ref_n(x_59, 2);
lean_inc(x_54);
x_74 = l_Lean_Syntax_node2(x_54, x_73, x_59, x_59);
x_75 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__19));
lean_inc(x_54);
if (x_41 == 0)
{
lean_ctor_set_tag(x_40, 2);
lean_ctor_set(x_40, 1, x_75);
lean_ctor_set(x_40, 0, x_54);
x_76 = x_40;
goto block_299;
}
else
{
lean_object* x_300; 
x_300 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_300, 0, x_54);
lean_ctor_set(x_300, 1, x_75);
x_76 = x_300;
goto block_299;
}
block_299:
{
lean_object* x_77; lean_object* x_78; size_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_77 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__21));
x_78 = l_Array_zip___redArg(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
x_79 = lean_array_size(x_78);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_54);
x_80 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3(x_54, x_59, x_60, x_79, x_31, x_78);
x_81 = l_Array_append___redArg(x_58, x_80);
lean_dec_ref(x_80);
lean_inc(x_54);
x_82 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_82, 0, x_54);
lean_ctor_set(x_82, 1, x_55);
lean_ctor_set(x_82, 2, x_81);
lean_inc(x_54);
x_83 = l_Lean_Syntax_node1(x_54, x_77, x_82);
lean_inc_ref(x_59);
lean_inc_ref(x_76);
lean_inc(x_54);
x_84 = l_Lean_Syntax_node3(x_54, x_55, x_76, x_59, x_83);
x_85 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__23));
x_86 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__24));
lean_inc(x_54);
if (x_38 == 0)
{
lean_ctor_set_tag(x_37, 2);
lean_ctor_set(x_37, 1, x_86);
lean_ctor_set(x_37, 0, x_54);
x_87 = x_37;
goto block_297;
}
else
{
lean_object* x_298; 
x_298 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_298, 0, x_54);
lean_ctor_set(x_298, 1, x_86);
x_87 = x_298;
goto block_297;
}
block_297:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; size_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; size_t x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_88 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26));
x_89 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__28, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__28_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__28);
x_90 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__29));
lean_inc(x_53);
lean_inc(x_52);
x_91 = l_Lean_addMacroScope(x_52, x_90, x_53);
x_92 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__34));
lean_inc(x_54);
x_93 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_93, 0, x_54);
lean_ctor_set(x_93, 1, x_89);
lean_ctor_set(x_93, 2, x_91);
lean_ctor_set(x_93, 3, x_92);
lean_inc_ref(x_59);
lean_inc(x_54);
x_94 = l_Lean_Syntax_node2(x_54, x_88, x_59, x_93);
x_95 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__35));
lean_inc(x_54);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_54);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__37, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__37_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__37);
x_98 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__38));
lean_inc(x_53);
lean_inc(x_52);
x_99 = l_Lean_addMacroScope(x_52, x_98, x_53);
x_100 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__43));
lean_inc(x_54);
x_101 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_101, 0, x_54);
lean_ctor_set(x_101, 1, x_97);
lean_ctor_set(x_101, 2, x_99);
lean_ctor_set(x_101, 3, x_100);
lean_inc_ref(x_59);
lean_inc(x_54);
x_102 = l_Lean_Syntax_node2(x_54, x_88, x_59, x_101);
lean_inc_ref(x_96);
lean_inc(x_54);
x_103 = l_Lean_Syntax_node3(x_54, x_55, x_94, x_96, x_102);
lean_inc(x_54);
x_104 = l_Lean_Syntax_node2(x_54, x_55, x_87, x_103);
lean_inc(x_54);
x_105 = l_Lean_Syntax_node1(x_54, x_85, x_104);
lean_inc_ref(x_59);
lean_inc(x_54);
x_106 = l_Lean_Syntax_node6(x_54, x_62, x_65, x_72, x_74, x_59, x_84, x_105);
lean_inc(x_60);
lean_inc(x_54);
x_107 = l_Lean_Syntax_node2(x_54, x_56, x_60, x_106);
x_108 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__44));
x_109 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45));
x_110 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__46));
x_111 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47));
lean_inc(x_54);
x_112 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_112, 0, x_54);
lean_ctor_set(x_112, 1, x_110);
x_113 = l_Array_append___redArg(x_58, x_3);
lean_inc(x_54);
x_114 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_114, 0, x_54);
lean_ctor_set(x_114, 1, x_55);
lean_ctor_set(x_114, 2, x_113);
lean_inc(x_54);
x_115 = l_Lean_Syntax_node2(x_54, x_111, x_112, x_114);
lean_inc(x_54);
x_116 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_116, 0, x_54);
lean_ctor_set(x_116, 1, x_108);
x_117 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__48));
x_118 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49));
x_119 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51));
lean_inc_ref(x_59);
lean_inc(x_54);
x_120 = l_Lean_Syntax_node1(x_54, x_119, x_59);
lean_inc(x_54);
x_121 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_121, 0, x_54);
lean_ctor_set(x_121, 1, x_117);
x_122 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__53));
x_123 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12));
x_124 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__13));
lean_inc(x_54);
x_125 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_125, 0, x_54);
lean_ctor_set(x_125, 1, x_124);
x_126 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18));
x_127 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__54, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__54_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__54);
x_128 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__55));
lean_inc(x_53);
lean_inc(x_52);
x_129 = l_Lean_addMacroScope(x_52, x_128, x_53);
x_130 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__58));
lean_inc(x_54);
x_131 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_131, 0, x_54);
lean_ctor_set(x_131, 1, x_127);
lean_ctor_set(x_131, 2, x_129);
lean_ctor_set(x_131, 3, x_130);
x_132 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51));
x_133 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53));
x_134 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__9));
lean_inc(x_54);
x_135 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_135, 0, x_54);
lean_ctor_set(x_135, 1, x_134);
x_136 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55));
x_137 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56);
x_138 = lean_box(0);
lean_inc(x_53);
lean_inc(x_52);
x_139 = l_Lean_addMacroScope(x_52, x_138, x_53);
x_140 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__64));
lean_inc(x_54);
x_141 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_141, 0, x_54);
lean_ctor_set(x_141, 1, x_137);
lean_ctor_set(x_141, 2, x_139);
lean_ctor_set(x_141, 3, x_140);
lean_inc(x_54);
x_142 = l_Lean_Syntax_node1(x_54, x_136, x_141);
lean_inc(x_54);
x_143 = l_Lean_Syntax_node2(x_54, x_133, x_135, x_142);
x_144 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__66));
x_145 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__67));
lean_inc(x_54);
x_146 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_146, 0, x_54);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Lean_mkCIdent(x_17);
lean_inc(x_54);
x_148 = l_Lean_Syntax_node2(x_54, x_144, x_146, x_147);
x_149 = lean_array_size(x_48);
x_150 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__4(x_149, x_31, x_48);
x_151 = l_Array_append___redArg(x_58, x_150);
lean_dec_ref(x_150);
lean_inc(x_54);
x_152 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_152, 0, x_54);
lean_ctor_set(x_152, 1, x_55);
lean_ctor_set(x_152, 2, x_151);
lean_inc(x_54);
x_153 = l_Lean_Syntax_node2(x_54, x_126, x_148, x_152);
x_154 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__14));
lean_inc(x_54);
x_155 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_155, 0, x_54);
lean_ctor_set(x_155, 1, x_154);
lean_inc(x_54);
x_156 = l_Lean_Syntax_node3(x_54, x_132, x_143, x_153, x_155);
lean_inc(x_54);
x_157 = l_Lean_Syntax_node1(x_54, x_55, x_156);
lean_inc(x_54);
x_158 = l_Lean_Syntax_node2(x_54, x_126, x_131, x_157);
lean_inc_ref(x_125);
lean_inc(x_54);
x_159 = l_Lean_Syntax_node2(x_54, x_123, x_125, x_158);
lean_inc_ref(x_59);
lean_inc(x_54);
x_160 = l_Lean_Syntax_node2(x_54, x_122, x_59, x_159);
x_161 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69));
x_162 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13));
lean_inc(x_54);
x_163 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_163, 0, x_54);
lean_ctor_set(x_163, 1, x_162);
x_164 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__71));
x_165 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__72));
lean_inc(x_54);
x_166 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_166, 0, x_54);
lean_ctor_set(x_166, 1, x_165);
x_167 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__74));
x_168 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__7));
x_169 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__9));
x_170 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20);
x_171 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21));
lean_inc(x_53);
lean_inc(x_52);
x_172 = l_Lean_addMacroScope(x_52, x_171, x_53);
x_173 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__76));
lean_inc(x_54);
x_174 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_174, 0, x_54);
lean_ctor_set(x_174, 1, x_170);
lean_ctor_set(x_174, 2, x_172);
lean_ctor_set(x_174, 3, x_173);
lean_inc_ref(x_59);
lean_inc(x_54);
x_175 = l_Lean_Syntax_node2(x_54, x_169, x_174, x_59);
x_176 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__12));
x_177 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__78, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__78_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__78);
x_178 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__79));
lean_inc(x_53);
lean_inc(x_52);
x_179 = l_Lean_addMacroScope(x_52, x_178, x_53);
lean_inc(x_54);
x_180 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_180, 0, x_54);
lean_ctor_set(x_180, 1, x_177);
lean_ctor_set(x_180, 2, x_179);
lean_ctor_set(x_180, 3, x_70);
lean_inc_ref(x_180);
lean_inc_ref(x_59);
lean_inc_ref(x_163);
lean_inc(x_54);
x_181 = l_Lean_Syntax_node3(x_54, x_176, x_163, x_59, x_180);
lean_inc_ref_n(x_59, 2);
lean_inc(x_54);
x_182 = l_Lean_Syntax_node3(x_54, x_55, x_59, x_59, x_181);
lean_inc(x_54);
x_183 = l_Lean_Syntax_node2(x_54, x_168, x_175, x_182);
x_184 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36);
x_185 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37));
lean_inc(x_53);
lean_inc(x_52);
x_186 = l_Lean_addMacroScope(x_52, x_185, x_53);
x_187 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__81));
lean_inc(x_54);
x_188 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_188, 0, x_54);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set(x_188, 2, x_186);
lean_ctor_set(x_188, 3, x_187);
lean_inc_ref(x_59);
lean_inc(x_54);
x_189 = l_Lean_Syntax_node2(x_54, x_169, x_188, x_59);
x_190 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__83, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__83_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__83);
x_191 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__84));
lean_inc(x_53);
lean_inc(x_52);
x_192 = l_Lean_addMacroScope(x_52, x_191, x_53);
lean_inc(x_54);
x_193 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_193, 0, x_54);
lean_ctor_set(x_193, 1, x_190);
lean_ctor_set(x_193, 2, x_192);
lean_ctor_set(x_193, 3, x_70);
lean_inc_ref(x_193);
lean_inc_ref(x_59);
lean_inc_ref(x_163);
lean_inc(x_54);
x_194 = l_Lean_Syntax_node3(x_54, x_176, x_163, x_59, x_193);
lean_inc_ref_n(x_59, 2);
lean_inc(x_54);
x_195 = l_Lean_Syntax_node3(x_54, x_55, x_59, x_59, x_194);
lean_inc(x_54);
x_196 = l_Lean_Syntax_node2(x_54, x_168, x_189, x_195);
lean_inc(x_54);
x_197 = l_Lean_Syntax_node3(x_54, x_55, x_183, x_96, x_196);
lean_inc(x_54);
x_198 = l_Lean_Syntax_node1(x_54, x_167, x_197);
x_199 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__86));
lean_inc_ref(x_59);
lean_inc(x_54);
x_200 = l_Lean_Syntax_node1(x_54, x_199, x_59);
x_201 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__87));
lean_inc(x_54);
x_202 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_202, 0, x_54);
lean_ctor_set(x_202, 1, x_201);
lean_inc_ref(x_202);
lean_inc(x_200);
lean_inc_ref_n(x_59, 2);
lean_inc_ref(x_166);
lean_inc(x_54);
x_203 = l_Lean_Syntax_node6(x_54, x_164, x_166, x_59, x_198, x_200, x_59, x_202);
x_204 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90));
lean_inc_ref_n(x_59, 2);
lean_inc(x_54);
x_205 = l_Lean_Syntax_node2(x_54, x_204, x_59, x_59);
x_206 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92));
x_207 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94));
x_208 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96));
x_209 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98));
x_210 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100));
lean_inc(x_54);
x_211 = l_Lean_Syntax_node1(x_54, x_210, x_180);
x_212 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__29, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__29);
x_213 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__30));
lean_inc(x_53);
lean_inc(x_52);
x_214 = l_Lean_addMacroScope(x_52, x_213, x_53);
lean_inc(x_54);
x_215 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_215, 0, x_54);
lean_ctor_set(x_215, 1, x_212);
lean_ctor_set(x_215, 2, x_214);
lean_ctor_set(x_215, 3, x_70);
lean_inc_ref(x_215);
lean_inc(x_54);
x_216 = l_Lean_Syntax_node1(x_54, x_55, x_215);
x_217 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__102));
x_218 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__103));
lean_inc(x_54);
x_219 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_219, 0, x_54);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__105, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__105_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__105);
x_221 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__106));
lean_inc(x_53);
lean_inc(x_52);
x_222 = l_Lean_addMacroScope(x_52, x_221, x_53);
x_223 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__109));
lean_inc(x_54);
x_224 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_224, 0, x_54);
lean_ctor_set(x_224, 1, x_220);
lean_ctor_set(x_224, 2, x_222);
lean_ctor_set(x_224, 3, x_223);
x_225 = lean_array_size(x_39);
x_226 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5(x_225, x_31, x_39);
x_227 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__110, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__110_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__110);
x_228 = l_Lean_mkSepArray(x_226, x_227);
lean_dec_ref(x_226);
x_229 = l_Array_append___redArg(x_58, x_228);
lean_dec_ref(x_228);
lean_inc(x_54);
x_230 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_230, 0, x_54);
lean_ctor_set(x_230, 1, x_55);
lean_ctor_set(x_230, 2, x_229);
lean_inc(x_54);
x_231 = l_Lean_Syntax_node1(x_54, x_167, x_230);
lean_inc_ref(x_71);
lean_inc_ref(x_125);
lean_inc(x_54);
x_232 = l_Lean_Syntax_node2(x_54, x_55, x_125, x_71);
lean_inc_ref(x_202);
lean_inc(x_200);
lean_inc_ref(x_59);
lean_inc_ref(x_166);
lean_inc(x_54);
x_233 = l_Lean_Syntax_node6(x_54, x_164, x_166, x_59, x_231, x_200, x_232, x_202);
lean_inc(x_54);
x_234 = l_Lean_Syntax_node1(x_54, x_55, x_233);
lean_inc(x_54);
x_235 = l_Lean_Syntax_node2(x_54, x_126, x_224, x_234);
lean_inc(x_54);
x_236 = l_Lean_Syntax_node1(x_54, x_55, x_235);
lean_inc_ref(x_219);
lean_inc(x_54);
x_237 = l_Lean_Syntax_node2(x_54, x_217, x_219, x_236);
lean_inc_ref(x_163);
lean_inc_ref(x_59);
lean_inc(x_54);
x_238 = l_Lean_Syntax_node5(x_54, x_209, x_211, x_216, x_59, x_163, x_237);
lean_inc(x_54);
x_239 = l_Lean_Syntax_node1(x_54, x_208, x_238);
lean_inc(x_205);
lean_inc_ref_n(x_59, 2);
lean_inc(x_54);
x_240 = l_Lean_Syntax_node4(x_54, x_207, x_59, x_59, x_239, x_205);
lean_inc(x_54);
x_241 = l_Lean_Syntax_node1(x_54, x_210, x_193);
x_242 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__112, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__112_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__112);
x_243 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__113));
lean_inc(x_53);
lean_inc(x_52);
x_244 = l_Lean_addMacroScope(x_52, x_243, x_53);
lean_inc(x_54);
x_245 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_245, 0, x_54);
lean_ctor_set(x_245, 1, x_242);
lean_ctor_set(x_245, 2, x_244);
lean_ctor_set(x_245, 3, x_70);
lean_inc(x_54);
x_246 = l_Lean_Syntax_node1(x_54, x_55, x_245);
x_247 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__114));
x_248 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115));
lean_inc(x_54);
x_249 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_249, 0, x_54);
lean_ctor_set(x_249, 1, x_247);
x_250 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117));
x_251 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119));
x_252 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__121));
x_253 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__122));
lean_inc(x_54);
x_254 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_254, 0, x_54);
lean_ctor_set(x_254, 1, x_253);
x_255 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124));
lean_inc(x_54);
x_256 = l_Lean_Syntax_node2(x_54, x_123, x_125, x_71);
lean_inc(x_54);
x_257 = l_Lean_Syntax_node1(x_54, x_55, x_256);
x_258 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16));
lean_inc(x_54);
x_259 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_259, 0, x_54);
lean_ctor_set(x_259, 1, x_258);
x_260 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126));
x_261 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128);
x_262 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__129));
x_263 = l_Lean_addMacroScope(x_52, x_262, x_53);
x_264 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__132));
lean_inc(x_54);
x_265 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_265, 0, x_54);
lean_ctor_set(x_265, 1, x_261);
lean_ctor_set(x_265, 2, x_263);
lean_ctor_set(x_265, 3, x_264);
lean_inc(x_246);
lean_inc(x_54);
x_266 = l_Lean_Syntax_node2(x_54, x_126, x_265, x_246);
lean_inc(x_54);
x_267 = l_Lean_Syntax_node1(x_54, x_260, x_266);
lean_inc(x_54);
x_268 = l_Lean_Syntax_node4(x_54, x_255, x_215, x_257, x_259, x_267);
lean_inc_ref(x_59);
lean_inc(x_54);
x_269 = l_Lean_Syntax_node3(x_54, x_252, x_254, x_59, x_268);
lean_inc_ref(x_59);
lean_inc(x_54);
x_270 = l_Lean_Syntax_node2(x_54, x_251, x_269, x_59);
x_271 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__134));
x_272 = l_Lean_Syntax_SepArray_ofElems(x_95, x_36);
lean_dec(x_36);
x_273 = l_Array_append___redArg(x_58, x_272);
lean_dec_ref(x_272);
lean_inc(x_54);
x_274 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_274, 0, x_54);
lean_ctor_set(x_274, 1, x_55);
lean_ctor_set(x_274, 2, x_273);
lean_inc(x_54);
x_275 = l_Lean_Syntax_node1(x_54, x_167, x_274);
lean_inc_ref_n(x_59, 2);
lean_inc(x_54);
x_276 = l_Lean_Syntax_node6(x_54, x_164, x_166, x_59, x_275, x_200, x_59, x_202);
lean_inc(x_54);
x_277 = l_Lean_Syntax_node1(x_54, x_55, x_276);
lean_inc(x_54);
x_278 = l_Lean_Syntax_node2(x_54, x_271, x_219, x_277);
lean_inc_ref(x_59);
lean_inc(x_54);
x_279 = l_Lean_Syntax_node2(x_54, x_251, x_278, x_59);
lean_inc(x_54);
x_280 = l_Lean_Syntax_node2(x_54, x_55, x_270, x_279);
lean_inc(x_54);
x_281 = l_Lean_Syntax_node1(x_54, x_250, x_280);
lean_inc(x_54);
x_282 = l_Lean_Syntax_node2(x_54, x_248, x_249, x_281);
lean_inc_ref(x_163);
lean_inc_ref(x_59);
lean_inc(x_54);
x_283 = l_Lean_Syntax_node5(x_54, x_209, x_241, x_246, x_59, x_163, x_282);
lean_inc(x_54);
x_284 = l_Lean_Syntax_node1(x_54, x_208, x_283);
lean_inc(x_205);
lean_inc_ref_n(x_59, 2);
lean_inc(x_54);
x_285 = l_Lean_Syntax_node4(x_54, x_207, x_59, x_59, x_284, x_205);
lean_inc_ref(x_59);
lean_inc(x_54);
x_286 = l_Lean_Syntax_node3(x_54, x_55, x_240, x_59, x_285);
lean_inc_ref(x_59);
lean_inc(x_54);
x_287 = l_Lean_Syntax_node3(x_54, x_206, x_76, x_286, x_59);
lean_inc(x_54);
x_288 = l_Lean_Syntax_node1(x_54, x_55, x_287);
lean_inc(x_54);
x_289 = l_Lean_Syntax_node4(x_54, x_161, x_163, x_203, x_205, x_288);
lean_inc_ref(x_59);
lean_inc(x_54);
x_290 = l_Lean_Syntax_node6(x_54, x_118, x_120, x_121, x_59, x_59, x_160, x_289);
lean_inc(x_54);
x_291 = l_Lean_Syntax_node2(x_54, x_56, x_60, x_290);
lean_inc(x_54);
x_292 = l_Lean_Syntax_node3(x_54, x_109, x_115, x_116, x_291);
x_293 = l_Lean_Syntax_node2(x_54, x_55, x_107, x_292);
if (x_50 == 0)
{
lean_ctor_set(x_49, 0, x_293);
x_294 = x_49;
goto block_295;
}
else
{
lean_object* x_296; 
x_296 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_296, 0, x_293);
x_294 = x_296;
goto block_295;
}
block_295:
{
return x_294;
}
}
}
}
}
}
}
else
{
lean_object* x_307; lean_object* x_308; uint8_t x_309; uint8_t x_314; 
lean_del_object(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_del_object(x_40);
lean_dec(x_39);
lean_del_object(x_37);
lean_dec(x_36);
lean_dec_ref(x_26);
lean_del_object(x_18);
lean_dec(x_17);
x_307 = lean_ctor_get(x_47, 0);
x_314 = !lean_is_exclusive(x_47);
if (x_314 == 0)
{
x_308 = x_47;
x_309 = x_314;
goto block_313;
}
else
{
lean_inc(x_307);
lean_dec(x_47);
x_308 = lean_box(0);
x_309 = x_314;
goto block_313;
}
block_313:
{
lean_object* x_310; 
if (x_309 == 0)
{
x_310 = x_308;
goto block_311;
}
else
{
lean_object* x_312; 
x_312 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_312, 0, x_307);
x_310 = x_312;
goto block_311;
}
block_311:
{
return x_310;
}
}
}
}
}
}
}
else
{
lean_object* x_323; lean_object* x_324; uint8_t x_325; uint8_t x_330; 
lean_dec_ref(x_26);
lean_dec_ref(x_24);
lean_del_object(x_18);
lean_dec(x_17);
lean_dec_ref(x_2);
x_323 = lean_ctor_get(x_32, 0);
x_330 = !lean_is_exclusive(x_32);
if (x_330 == 0)
{
x_324 = x_32;
x_325 = x_330;
goto block_329;
}
else
{
lean_inc(x_323);
lean_dec(x_32);
x_324 = lean_box(0);
x_325 = x_330;
goto block_329;
}
block_329:
{
lean_object* x_326; 
if (x_325 == 0)
{
x_326 = x_324;
goto block_327;
}
else
{
lean_object* x_328; 
x_328 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_328, 0, x_323);
x_326 = x_328;
goto block_327;
}
block_327:
{
return x_326;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___redArg(x_1, x_2, x_3, x_6, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg(x_1, x_2, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Parser_termParser(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__0, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__0_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__0);
x_2 = l_Lean_Parser_Term_matchAlt(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__1, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__1_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm___closed__1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_instCoeTSyntaxConsSyntaxNodeKindStrNumAnonymousOfNatNatNilMkStr4___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 10);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 11);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = l_Lean_addMacroScope(x_5, x_1, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__2));
x_5 = l_Lean_Core_withFreshMacroScope___redArg(x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg(x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_4, x_5, x_2, x_3, x_6, x_7, x_8, x_9, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___redArg___lam__0___boxed), 10, 3);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), x_1, x_12, x_3, x_4, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
x_15 = x_13;
x_16 = x_21;
goto block_20;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_4);
x_14 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___redArg(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_4);
x_14 = lean_unbox(x_5);
x_15 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_102; 
x_9 = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__0);
x_10 = l_ReaderT_instMonad___redArg(x_9);
x_11 = lean_ctor_get(x_10, 0);
x_102 = !lean_is_exclusive(x_10);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_10, 1);
lean_dec(x_103);
x_12 = x_10;
x_13 = x_102;
goto block_101;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_99; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 2);
x_16 = lean_ctor_get(x_11, 3);
x_17 = lean_ctor_get(x_11, 4);
x_99 = !lean_is_exclusive(x_11);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_11, 1);
lean_dec(x_100);
x_18 = x_11;
x_19 = x_99;
goto block_98;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__1));
x_21 = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__2));
lean_inc_ref(x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_22, 0, x_14);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_17);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_16);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_27, 0, x_15);
if (x_19 == 0)
{
lean_ctor_set(x_18, 4, x_25);
lean_ctor_set(x_18, 3, x_26);
lean_ctor_set(x_18, 2, x_27);
lean_ctor_set(x_18, 1, x_20);
lean_ctor_set(x_18, 0, x_24);
x_28 = x_18;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_97, 0, x_24);
lean_ctor_set(x_97, 1, x_20);
lean_ctor_set(x_97, 2, x_27);
lean_ctor_set(x_97, 3, x_26);
lean_ctor_set(x_97, 4, x_25);
x_28 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_29; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_21);
lean_ctor_set(x_12, 0, x_28);
x_29 = x_12;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_28);
lean_ctor_set(x_95, 1, x_21);
x_29 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_92; 
x_30 = l_ReaderT_instMonad___redArg(x_29);
x_31 = lean_ctor_get(x_30, 0);
x_92 = !lean_is_exclusive(x_30);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_30, 1);
lean_dec(x_93);
x_32 = x_30;
x_33 = x_92;
goto block_91;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_89; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 2);
x_36 = lean_ctor_get(x_31, 3);
x_37 = lean_ctor_get(x_31, 4);
x_89 = !lean_is_exclusive(x_31);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_31, 1);
lean_dec(x_90);
x_38 = x_31;
x_39 = x_89;
goto block_88;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__3));
x_41 = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__4));
lean_inc_ref(x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_42, 0, x_34);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_34);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_45, 0, x_37);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_46, 0, x_36);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_47, 0, x_35);
if (x_39 == 0)
{
lean_ctor_set(x_38, 4, x_45);
lean_ctor_set(x_38, 3, x_46);
lean_ctor_set(x_38, 2, x_47);
lean_ctor_set(x_38, 1, x_40);
lean_ctor_set(x_38, 0, x_44);
x_48 = x_38;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_87, 0, x_44);
lean_ctor_set(x_87, 1, x_40);
lean_ctor_set(x_87, 2, x_47);
lean_ctor_set(x_87, 3, x_46);
lean_ctor_set(x_87, 4, x_45);
x_48 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_49; 
if (x_33 == 0)
{
lean_ctor_set(x_32, 1, x_41);
lean_ctor_set(x_32, 0, x_48);
x_49 = x_32;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_48);
lean_ctor_set(x_85, 1, x_41);
x_49 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_82; 
x_50 = l_ReaderT_instMonad___redArg(x_49);
x_51 = lean_ctor_get(x_50, 0);
x_82 = !lean_is_exclusive(x_50);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_50, 1);
lean_dec(x_83);
x_52 = x_50;
x_53 = x_82;
goto block_81;
}
else
{
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_79; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get(x_51, 2);
x_56 = lean_ctor_get(x_51, 3);
x_57 = lean_ctor_get(x_51, 4);
x_79 = !lean_is_exclusive(x_51);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_51, 1);
lean_dec(x_80);
x_58 = x_51;
x_59 = x_79;
goto block_78;
}
else
{
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_51);
x_58 = lean_box(0);
x_59 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_60 = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__5));
x_61 = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___closed__6));
lean_inc_ref(x_54);
x_62 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_62, 0, x_54);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_63, 0, x_54);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_65, 0, x_57);
x_66 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_66, 0, x_56);
x_67 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_67, 0, x_55);
if (x_59 == 0)
{
lean_ctor_set(x_58, 4, x_65);
lean_ctor_set(x_58, 3, x_66);
lean_ctor_set(x_58, 2, x_67);
lean_ctor_set(x_58, 1, x_60);
lean_ctor_set(x_58, 0, x_64);
x_68 = x_58;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_77, 0, x_64);
lean_ctor_set(x_77, 1, x_60);
lean_ctor_set(x_77, 2, x_67);
lean_ctor_set(x_77, 3, x_66);
lean_ctor_set(x_77, 4, x_65);
x_68 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_69; 
if (x_53 == 0)
{
lean_ctor_set(x_52, 1, x_61);
lean_ctor_set(x_52, 0, x_68);
x_69 = x_52;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_68);
lean_ctor_set(x_75, 1, x_61);
x_69 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_box(0);
x_71 = l_instInhabitedOfMonad___redArg(x_69, x_70);
x_72 = lean_panic_fn(x_71, x_1);
x_73 = lean_apply_7(x_72, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_73;
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
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__13(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__13___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__13(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__2));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_26; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
x_5 = x_2;
x_6 = x_26;
goto block_25;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_23; 
x_7 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_3, 1);
lean_dec(x_24);
x_8 = x_3;
x_9 = x_23;
goto block_22;
}
else
{
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__0);
if (x_9 == 0)
{
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_10);
lean_ctor_set(x_8, 0, x_1);
x_11 = x_8;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_10);
x_11 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__3);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_12);
lean_ctor_set(x_5, 0, x_11);
x_13 = x_5;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_12);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_MessageData_ofSyntax(x_7);
x_15 = l_Lean_indentD(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_1 = x_16;
x_2 = x_4;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lean_Elab_pp_macroStack;
x_7 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__13(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_26; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_10, 0);
lean_dec(x_27);
x_12 = x_10;
x_13 = x_26;
goto block_25;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__0);
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_14);
lean_ctor_set(x_12, 0, x_1);
x_15 = x_12;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_14);
x_15 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg___closed__2);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_MessageData_ofSyntax(x_11);
x_19 = l_Lean_indentD(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14(x_20, x_2);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_23; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7_spec__7(x_1, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
lean_inc(x_12);
x_13 = l_Lean_Elab_getBetterRef(x_9, x_12);
x_14 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg(x_11, x_12, x_6);
x_15 = lean_ctor_get(x_14, 0);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
x_16 = x_14;
x_17 = x_23;
goto block_22;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_15);
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__6));
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(121u);
x_4 = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__5));
x_5 = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__4));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_st_ref_get(x_7);
x_19 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_19);
lean_dec(x_18);
x_20 = 0;
lean_inc(x_1);
x_21 = l_Lean_Environment_findAsync_x3f(x_19, x_1, x_20);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_ctor_get_uint8(x_22, sizeof(void*)*3);
if (x_23 == 6)
{
lean_object* x_24; 
x_24 = l_Lean_AsyncConstantInfo_toConstantInfo(x_22);
if (lean_obj_tag(x_24) == 6)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_25 = lean_ctor_get(x_24, 0);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
x_26 = x_24;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
lean_ctor_set_tag(x_26, 0);
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_24);
x_33 = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__7);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_34 = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10_spec__13(x_33, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_43; 
x_35 = lean_ctor_get(x_34, 0);
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
x_36 = x_34;
x_37 = x_43;
goto block_42;
}
else
{
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = x_43;
goto block_42;
}
block_42:
{
if (lean_obj_tag(x_35) == 0)
{
lean_del_object(x_36);
x_9 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec_ref(x_35);
if (x_37 == 0)
{
lean_ctor_set(x_36, 0, x_38);
x_39 = x_36;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_38);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_51; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_44 = lean_ctor_get(x_34, 0);
x_51 = !lean_is_exclusive(x_34);
if (x_51 == 0)
{
x_45 = x_34;
x_46 = x_51;
goto block_50;
}
else
{
lean_inc(x_44);
lean_dec(x_34);
x_45 = lean_box(0);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_46 == 0)
{
x_47 = x_45;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_44);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
}
else
{
lean_dec(x_22);
x_9 = lean_box(0);
goto block_17;
}
}
else
{
lean_dec(x_21);
x_9 = lean_box(0);
goto block_17;
}
block_17:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__1);
x_11 = 0;
x_12 = l_Lean_MessageData_ofConstName(x_1, x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__3);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___redArg(x_15, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__5(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec_ref(x_8);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
else
{
lean_object* x_13; 
lean_inc(x_9);
lean_inc_ref(x_8);
x_13 = l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg(x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = lean_mk_syntax_ident(x_14);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_16, x_2, x_17);
x_2 = x_19;
x_3 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_3);
x_22 = lean_ctor_get(x_13, 0);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
x_23 = x_13;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__5(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec_ref(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
x_8 = lean_ctor_get(x_4, 5);
x_9 = lean_ctor_get(x_4, 10);
x_10 = lean_ctor_get(x_4, 11);
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = 0;
x_15 = l_Lean_SourceInfo_fromRef(x_8, x_14);
x_16 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15));
x_17 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16));
lean_inc(x_15);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18));
x_20 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36);
x_21 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37));
lean_inc(x_10);
lean_inc(x_9);
x_22 = l_Lean_addMacroScope(x_9, x_21, x_10);
x_23 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__40));
lean_inc(x_15);
x_24 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
x_25 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
lean_inc(x_15);
x_26 = l_Lean_Syntax_node1(x_15, x_25, x_11);
lean_inc(x_15);
x_27 = l_Lean_Syntax_node2(x_15, x_19, x_24, x_26);
x_28 = l_Lean_Syntax_node2(x_15, x_16, x_18, x_27);
x_29 = 1;
x_30 = lean_usize_add(x_2, x_29);
x_31 = lean_array_uset(x_13, x_2, x_28);
x_2 = x_30;
x_3 = x_31;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___redArg(x_6, x_7, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_8);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; 
x_13 = lean_ctor_get(x_8, 5);
x_14 = lean_ctor_get(x_8, 10);
x_15 = lean_ctor_get(x_8, 11);
x_16 = lean_array_uget(x_3, x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_3, x_2, x_17);
x_19 = 0;
x_20 = l_Lean_SourceInfo_fromRef(x_13, x_19);
x_21 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15));
x_22 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16));
lean_inc(x_20);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18));
x_25 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36);
x_26 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37));
lean_inc(x_15);
lean_inc(x_14);
x_27 = l_Lean_addMacroScope(x_14, x_26, x_15);
x_28 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__40));
lean_inc(x_20);
x_29 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set(x_29, 3, x_28);
x_30 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
lean_inc(x_20);
x_31 = l_Lean_Syntax_node1(x_20, x_30, x_16);
lean_inc(x_20);
x_32 = l_Lean_Syntax_node2(x_20, x_24, x_29, x_31);
x_33 = l_Lean_Syntax_node2(x_20, x_21, x_23, x_32);
x_34 = 1;
x_35 = lean_usize_add(x_2, x_34);
x_36 = lean_array_uset(x_18, x_2, x_33);
x_37 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___redArg(x_1, x_35, x_36, x_8);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget_borrowed(x_3, x_2);
lean_inc_ref(x_4);
x_11 = l_Lean_Meta_getFVarLocalDecl___redArg(x_10, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_ctor_get(x_5, 5);
x_14 = lean_ctor_get(x_5, 10);
x_15 = lean_ctor_get(x_5, 11);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = l_Lean_LocalDecl_userName(x_12);
lean_dec(x_12);
x_19 = 0;
x_20 = l_Lean_SourceInfo_fromRef(x_13, x_19);
x_21 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___redArg___closed__1));
x_22 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__9));
lean_inc(x_20);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
x_25 = lean_mk_syntax_ident(x_18);
lean_inc(x_20);
x_26 = l_Lean_Syntax_node1(x_20, x_24, x_25);
x_27 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__13));
lean_inc(x_20);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__2);
x_30 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__3));
lean_inc(x_15);
lean_inc(x_14);
x_31 = l_Lean_addMacroScope(x_14, x_30, x_15);
x_32 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__34));
lean_inc(x_20);
x_33 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set(x_33, 3, x_32);
lean_inc(x_20);
x_34 = l_Lean_Syntax_node2(x_20, x_24, x_28, x_33);
x_35 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10);
lean_inc(x_20);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_24);
lean_ctor_set(x_36, 2, x_35);
x_37 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__14));
lean_inc(x_20);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_20);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Syntax_node5(x_20, x_21, x_23, x_26, x_34, x_36, x_38);
x_40 = 1;
x_41 = lean_usize_add(x_2, x_40);
x_42 = lean_array_uset(x_17, x_2, x_39);
x_2 = x_41;
x_3 = x_42;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_51; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_44 = lean_ctor_get(x_11, 0);
x_51 = !lean_is_exclusive(x_11);
if (x_51 == 0)
{
x_45 = x_11;
x_46 = x_51;
goto block_50;
}
else
{
lean_inc(x_44);
lean_dec(x_11);
x_45 = lean_box(0);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_46 == 0)
{
x_47 = x_45;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_44);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___redArg(x_8, x_9, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec_ref(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
x_8 = lean_ctor_get(x_4, 5);
x_9 = lean_ctor_get(x_4, 10);
x_10 = lean_ctor_get(x_4, 11);
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = 0;
x_15 = l_Lean_SourceInfo_fromRef(x_8, x_14);
x_16 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15));
x_17 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16));
lean_inc(x_15);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18));
x_20 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20);
x_21 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21));
lean_inc(x_10);
lean_inc(x_9);
x_22 = l_Lean_addMacroScope(x_9, x_21, x_10);
x_23 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__25));
lean_inc(x_15);
x_24 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
x_25 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
lean_inc(x_15);
x_26 = l_Lean_Syntax_node1(x_15, x_25, x_11);
lean_inc(x_15);
x_27 = l_Lean_Syntax_node2(x_15, x_19, x_24, x_26);
x_28 = l_Lean_Syntax_node2(x_15, x_16, x_18, x_27);
x_29 = 1;
x_30 = lean_usize_add(x_2, x_29);
x_31 = lean_array_uset(x_13, x_2, x_28);
x_2 = x_30;
x_3 = x_31;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___redArg(x_6, x_7, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_8);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; 
x_13 = lean_ctor_get(x_8, 5);
x_14 = lean_ctor_get(x_8, 10);
x_15 = lean_ctor_get(x_8, 11);
x_16 = lean_array_uget(x_3, x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_3, x_2, x_17);
x_19 = 0;
x_20 = l_Lean_SourceInfo_fromRef(x_13, x_19);
x_21 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__15));
x_22 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16));
lean_inc(x_20);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18));
x_25 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20);
x_26 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21));
lean_inc(x_15);
lean_inc(x_14);
x_27 = l_Lean_addMacroScope(x_14, x_26, x_15);
x_28 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__25));
lean_inc(x_20);
x_29 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set(x_29, 3, x_28);
x_30 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
lean_inc(x_20);
x_31 = l_Lean_Syntax_node1(x_20, x_30, x_16);
lean_inc(x_20);
x_32 = l_Lean_Syntax_node2(x_20, x_24, x_29, x_31);
x_33 = l_Lean_Syntax_node2(x_20, x_21, x_23, x_32);
x_34 = 1;
x_35 = lean_usize_add(x_2, x_34);
x_36 = lean_array_uset(x_18, x_2, x_33);
x_37 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___redArg(x_1, x_35, x_36, x_8);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__6(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__6(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__4(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__10));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_1);
x_15 = lean_array_size(x_5);
x_16 = 0;
lean_inc_ref(x_11);
lean_inc_ref(x_9);
lean_inc_ref(x_5);
x_17 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___redArg(x_15, x_16, x_5, x_9, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; lean_object* x_35; size_t x_36; lean_object* x_37; size_t x_38; lean_object* x_39; size_t x_40; lean_object* x_41; lean_object* x_42; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_11, 5);
x_20 = lean_ctor_get(x_11, 10);
x_21 = lean_ctor_get(x_11, 11);
x_22 = 0;
x_23 = l_Lean_SourceInfo_fromRef(x_19, x_22);
x_24 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__0));
x_25 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__2));
x_26 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__1));
x_27 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
x_28 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10);
lean_inc(x_23);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
x_30 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__2));
lean_inc(x_23);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_30);
x_32 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9));
lean_inc_ref_n(x_29, 7);
lean_inc(x_23);
x_33 = l_Lean_Syntax_node7(x_23, x_32, x_29, x_29, x_29, x_29, x_29, x_29, x_29);
x_34 = lean_array_size(x_18);
x_35 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__2(x_34, x_16, x_18);
x_36 = lean_array_size(x_35);
x_37 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__3(x_36, x_16, x_35);
x_38 = lean_array_size(x_37);
x_39 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__4(x_38, x_16, x_37);
x_40 = lean_array_size(x_39);
x_41 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5(x_40, x_16, x_39);
lean_inc(x_12);
lean_inc_ref(x_11);
x_42 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__5(x_15, x_16, x_5, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; size_t x_44; lean_object* x_45; size_t x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = lean_array_size(x_43);
x_45 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__6(x_44, x_16, x_43);
x_46 = lean_array_size(x_45);
lean_inc_ref(x_11);
lean_inc_ref(x_45);
x_47 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7(x_46, x_16, x_45, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
lean_inc_ref(x_2);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_49 = lean_apply_7(x_2, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = l_Array_append___redArg(x_28, x_41);
lean_dec_ref(x_41);
lean_inc(x_23);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_23);
lean_ctor_set(x_52, 1, x_27);
lean_ctor_set(x_52, 2, x_51);
x_53 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__13));
lean_inc(x_23);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_23);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__17, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__17_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__17);
x_56 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6));
x_57 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__18));
lean_inc(x_21);
lean_inc(x_20);
x_58 = l_Lean_addMacroScope(x_20, x_57, x_21);
x_59 = lean_box(0);
lean_inc(x_58);
lean_inc(x_23);
x_60 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_60, 0, x_23);
lean_ctor_set(x_60, 1, x_55);
lean_ctor_set(x_60, 2, x_58);
lean_ctor_set(x_60, 3, x_59);
x_61 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__10));
x_62 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12));
lean_inc(x_23);
x_63 = l_Lean_Syntax_node2(x_23, x_62, x_54, x_60);
lean_inc(x_23);
x_64 = l_Lean_Syntax_node1(x_23, x_27, x_63);
x_65 = lean_box(0);
x_66 = l_Lean_Name_str___override(x_65, x_14);
x_67 = lean_mk_syntax_ident(x_66);
x_68 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__22));
x_69 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__4));
lean_inc(x_50);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_50);
lean_ctor_set(x_70, 1, x_30);
x_71 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18));
x_72 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__6));
x_73 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__31));
lean_inc(x_50);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_50);
lean_ctor_set(x_74, 1, x_73);
lean_inc(x_67);
lean_inc(x_50);
x_75 = l_Lean_Syntax_node2(x_50, x_72, x_74, x_67);
x_76 = l_Array_append___redArg(x_28, x_45);
lean_inc_ref(x_76);
lean_inc(x_50);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_50);
lean_ctor_set(x_77, 1, x_27);
lean_ctor_set(x_77, 2, x_76);
lean_inc(x_75);
lean_inc(x_50);
x_78 = l_Lean_Syntax_node2(x_50, x_71, x_75, x_77);
lean_inc(x_50);
x_79 = l_Lean_Syntax_node1(x_50, x_27, x_78);
lean_inc(x_50);
x_80 = l_Lean_Syntax_node1(x_50, x_27, x_79);
x_81 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__7));
lean_inc(x_50);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_50);
lean_ctor_set(x_82, 1, x_81);
x_83 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__102));
x_84 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__103));
lean_inc(x_50);
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_50);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__105, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__105_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__105);
x_87 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__106));
lean_inc(x_21);
lean_inc(x_20);
x_88 = l_Lean_addMacroScope(x_20, x_87, x_21);
x_89 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__109));
lean_inc(x_50);
x_90 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_90, 0, x_50);
lean_ctor_set(x_90, 1, x_86);
lean_ctor_set(x_90, 2, x_88);
lean_ctor_set(x_90, 3, x_89);
x_91 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__9));
x_92 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__53));
x_93 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__9));
lean_inc(x_50);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_50);
lean_ctor_set(x_94, 1, x_93);
x_95 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__55));
x_96 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__56);
lean_inc(x_21);
lean_inc(x_20);
x_97 = l_Lean_addMacroScope(x_20, x_65, x_21);
x_98 = l_Lean_Name_mkStr3(x_24, x_68, x_3);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__60));
lean_inc_ref(x_4);
x_101 = l_Lean_Name_mkStr3(x_24, x_4, x_61);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
lean_inc_ref(x_4);
x_103 = l_Lean_Name_mkStr3(x_24, x_4, x_25);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = l_Lean_Name_mkStr2(x_24, x_4);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_107 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__59));
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_102);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_100);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_99);
lean_ctor_set(x_112, 1, x_111);
lean_inc_ref(x_112);
lean_inc(x_97);
lean_inc(x_50);
x_113 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_113, 0, x_50);
lean_ctor_set(x_113, 1, x_96);
lean_ctor_set(x_113, 2, x_97);
lean_ctor_set(x_113, 3, x_112);
lean_inc(x_50);
x_114 = l_Lean_Syntax_node1(x_50, x_95, x_113);
lean_inc(x_50);
x_115 = l_Lean_Syntax_node2(x_50, x_92, x_94, x_114);
x_116 = l_Array_append___redArg(x_28, x_48);
lean_dec(x_48);
lean_inc(x_50);
x_117 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_117, 0, x_50);
lean_ctor_set(x_117, 1, x_27);
lean_ctor_set(x_117, 2, x_116);
lean_inc(x_50);
x_118 = l_Lean_Syntax_node2(x_50, x_71, x_75, x_117);
lean_inc(x_50);
x_119 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_119, 0, x_50);
lean_ctor_set(x_119, 1, x_53);
lean_inc(x_50);
x_120 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_120, 0, x_50);
lean_ctor_set(x_120, 1, x_55);
lean_ctor_set(x_120, 2, x_58);
lean_ctor_set(x_120, 3, x_59);
lean_inc(x_50);
x_121 = l_Lean_Syntax_node1(x_50, x_27, x_120);
lean_inc_ref(x_11);
x_122 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8(x_46, x_16, x_45, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec_ref(x_122);
x_124 = lean_apply_7(x_2, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_166; 
x_125 = lean_ctor_get(x_124, 0);
x_166 = !lean_is_exclusive(x_124);
if (x_166 == 0)
{
x_126 = x_124;
x_127 = x_166;
goto block_165;
}
else
{
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_box(0);
x_127 = x_166;
goto block_165;
}
block_165:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_128 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__14));
lean_inc(x_50);
x_129 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_129, 0, x_50);
lean_ctor_set(x_129, 1, x_128);
lean_inc(x_50);
x_130 = l_Lean_Syntax_node5(x_50, x_91, x_115, x_118, x_119, x_121, x_129);
lean_inc(x_50);
x_131 = l_Lean_Syntax_node1(x_50, x_27, x_130);
lean_inc(x_50);
x_132 = l_Lean_Syntax_node2(x_50, x_71, x_90, x_131);
lean_inc(x_50);
x_133 = l_Lean_Syntax_node1(x_50, x_27, x_132);
lean_inc(x_23);
x_134 = l_Lean_Syntax_node2(x_23, x_56, x_52, x_64);
lean_inc(x_50);
x_135 = l_Lean_Syntax_node2(x_50, x_83, x_85, x_133);
lean_inc(x_67);
x_136 = l_Lean_Syntax_node5(x_23, x_26, x_29, x_31, x_33, x_67, x_134);
x_137 = l_Lean_Syntax_node4(x_50, x_69, x_70, x_80, x_82, x_135);
lean_inc(x_125);
x_138 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_138, 0, x_125);
lean_ctor_set(x_138, 1, x_30);
lean_inc(x_125);
x_139 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_139, 0, x_125);
lean_ctor_set(x_139, 1, x_73);
lean_inc(x_125);
x_140 = l_Lean_Syntax_node2(x_125, x_72, x_139, x_67);
lean_inc(x_125);
x_141 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_141, 0, x_125);
lean_ctor_set(x_141, 1, x_27);
lean_ctor_set(x_141, 2, x_76);
lean_inc(x_140);
lean_inc(x_125);
x_142 = l_Lean_Syntax_node2(x_125, x_71, x_140, x_141);
lean_inc(x_125);
x_143 = l_Lean_Syntax_node1(x_125, x_27, x_142);
lean_inc(x_125);
x_144 = l_Lean_Syntax_node1(x_125, x_27, x_143);
lean_inc(x_125);
x_145 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_145, 0, x_125);
lean_ctor_set(x_145, 1, x_81);
lean_inc(x_125);
x_146 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_146, 0, x_125);
lean_ctor_set(x_146, 1, x_84);
x_147 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__51));
lean_inc(x_125);
x_148 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_148, 0, x_125);
lean_ctor_set(x_148, 1, x_93);
lean_inc(x_125);
x_149 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_149, 0, x_125);
lean_ctor_set(x_149, 1, x_96);
lean_ctor_set(x_149, 2, x_97);
lean_ctor_set(x_149, 3, x_112);
lean_inc(x_125);
x_150 = l_Lean_Syntax_node1(x_125, x_95, x_149);
lean_inc(x_125);
x_151 = l_Lean_Syntax_node2(x_125, x_92, x_148, x_150);
x_152 = l_Array_append___redArg(x_28, x_123);
lean_dec(x_123);
lean_inc(x_125);
x_153 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_153, 0, x_125);
lean_ctor_set(x_153, 1, x_27);
lean_ctor_set(x_153, 2, x_152);
lean_inc(x_125);
x_154 = l_Lean_Syntax_node2(x_125, x_71, x_140, x_153);
lean_inc(x_125);
x_155 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_155, 0, x_125);
lean_ctor_set(x_155, 1, x_128);
lean_inc(x_125);
x_156 = l_Lean_Syntax_node3(x_125, x_147, x_151, x_154, x_155);
lean_inc(x_125);
x_157 = l_Lean_Syntax_node1(x_125, x_27, x_156);
lean_inc(x_125);
x_158 = l_Lean_Syntax_node2(x_125, x_83, x_146, x_157);
x_159 = l_Lean_Syntax_node4(x_125, x_69, x_138, x_144, x_145, x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_137);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_136);
lean_ctor_set(x_161, 1, x_160);
if (x_127 == 0)
{
lean_ctor_set(x_126, 0, x_161);
x_162 = x_126;
goto block_163;
}
else
{
lean_object* x_164; 
x_164 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_164, 0, x_161);
x_162 = x_164;
goto block_163;
}
block_163:
{
return x_162;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_174; 
lean_dec(x_123);
lean_dec(x_121);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec(x_115);
lean_dec_ref(x_112);
lean_dec(x_97);
lean_dec_ref(x_90);
lean_dec_ref(x_85);
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec_ref(x_76);
lean_dec_ref(x_70);
lean_dec(x_67);
lean_dec(x_64);
lean_dec_ref(x_52);
lean_dec(x_50);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_29);
lean_dec(x_23);
x_167 = lean_ctor_get(x_124, 0);
x_174 = !lean_is_exclusive(x_124);
if (x_174 == 0)
{
x_168 = x_124;
x_169 = x_174;
goto block_173;
}
else
{
lean_inc(x_167);
lean_dec(x_124);
x_168 = lean_box(0);
x_169 = x_174;
goto block_173;
}
block_173:
{
lean_object* x_170; 
if (x_169 == 0)
{
x_170 = x_168;
goto block_171;
}
else
{
lean_object* x_172; 
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_167);
x_170 = x_172;
goto block_171;
}
block_171:
{
return x_170;
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; uint8_t x_182; 
lean_dec(x_121);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec(x_115);
lean_dec_ref(x_112);
lean_dec(x_97);
lean_dec_ref(x_90);
lean_dec_ref(x_85);
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec_ref(x_76);
lean_dec_ref(x_70);
lean_dec(x_67);
lean_dec(x_64);
lean_dec_ref(x_52);
lean_dec(x_50);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_29);
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_175 = lean_ctor_get(x_122, 0);
x_182 = !lean_is_exclusive(x_122);
if (x_182 == 0)
{
x_176 = x_122;
x_177 = x_182;
goto block_181;
}
else
{
lean_inc(x_175);
lean_dec(x_122);
x_176 = lean_box(0);
x_177 = x_182;
goto block_181;
}
block_181:
{
lean_object* x_178; 
if (x_177 == 0)
{
x_178 = x_176;
goto block_179;
}
else
{
lean_object* x_180; 
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_175);
x_178 = x_180;
goto block_179;
}
block_179:
{
return x_178;
}
}
}
}
else
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; uint8_t x_190; 
lean_dec(x_48);
lean_dec_ref(x_45);
lean_dec_ref(x_41);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_29);
lean_dec(x_23);
lean_dec_ref(x_14);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_183 = lean_ctor_get(x_49, 0);
x_190 = !lean_is_exclusive(x_49);
if (x_190 == 0)
{
x_184 = x_49;
x_185 = x_190;
goto block_189;
}
else
{
lean_inc(x_183);
lean_dec(x_49);
x_184 = lean_box(0);
x_185 = x_190;
goto block_189;
}
block_189:
{
lean_object* x_186; 
if (x_185 == 0)
{
x_186 = x_184;
goto block_187;
}
else
{
lean_object* x_188; 
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_183);
x_186 = x_188;
goto block_187;
}
block_187:
{
return x_186;
}
}
}
}
else
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_198; 
lean_dec_ref(x_45);
lean_dec_ref(x_41);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_29);
lean_dec(x_23);
lean_dec_ref(x_14);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_191 = lean_ctor_get(x_47, 0);
x_198 = !lean_is_exclusive(x_47);
if (x_198 == 0)
{
x_192 = x_47;
x_193 = x_198;
goto block_197;
}
else
{
lean_inc(x_191);
lean_dec(x_47);
x_192 = lean_box(0);
x_193 = x_198;
goto block_197;
}
block_197:
{
lean_object* x_194; 
if (x_193 == 0)
{
x_194 = x_192;
goto block_195;
}
else
{
lean_object* x_196; 
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_191);
x_194 = x_196;
goto block_195;
}
block_195:
{
return x_194;
}
}
}
}
else
{
lean_object* x_199; lean_object* x_200; uint8_t x_201; uint8_t x_206; 
lean_dec_ref(x_41);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_29);
lean_dec(x_23);
lean_dec_ref(x_14);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_199 = lean_ctor_get(x_42, 0);
x_206 = !lean_is_exclusive(x_42);
if (x_206 == 0)
{
x_200 = x_42;
x_201 = x_206;
goto block_205;
}
else
{
lean_inc(x_199);
lean_dec(x_42);
x_200 = lean_box(0);
x_201 = x_206;
goto block_205;
}
block_205:
{
lean_object* x_202; 
if (x_201 == 0)
{
x_202 = x_200;
goto block_203;
}
else
{
lean_object* x_204; 
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_199);
x_202 = x_204;
goto block_203;
}
block_203:
{
return x_202;
}
}
}
}
else
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; uint8_t x_214; 
lean_dec_ref(x_14);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_207 = lean_ctor_get(x_17, 0);
x_214 = !lean_is_exclusive(x_17);
if (x_214 == 0)
{
x_208 = x_17;
x_209 = x_214;
goto block_213;
}
else
{
lean_inc(x_207);
lean_dec(x_17);
x_208 = lean_box(0);
x_209 = x_214;
goto block_213;
}
block_213:
{
lean_object* x_210; 
if (x_209 == 0)
{
x_210 = x_208;
goto block_211;
}
else
{
lean_object* x_212; 
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_207);
x_210 = x_212;
goto block_211;
}
block_211:
{
return x_210;
}
}
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_215 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___closed__11);
x_216 = l_Lean_MessageData_ofName(x_1);
x_217 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
x_218 = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___redArg(x_217, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
return x_218;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget_borrowed(x_4, x_3);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_14);
x_15 = l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10(x_14, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 2);
lean_inc_ref(x_18);
lean_dec_ref(x_17);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_19 = l_Lean_Meta_instantiateForall(x_18, x_1, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___closed__0));
x_22 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__0));
x_23 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__49));
lean_inc(x_14);
x_24 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___lam__1___boxed), 13, 4);
lean_closure_set(x_24, 0, x_14);
lean_closure_set(x_24, 1, x_21);
lean_closure_set(x_24, 2, x_22);
lean_closure_set(x_24, 3, x_23);
x_25 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_26 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___redArg(x_20, x_24, x_25, x_25, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_array_uset(x_4, x_3, x_28);
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_32 = lean_array_uset(x_29, x_3, x_27);
x_3 = x_31;
x_4 = x_32;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_41; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_34 = lean_ctor_get(x_26, 0);
x_41 = !lean_is_exclusive(x_26);
if (x_41 == 0)
{
x_35 = x_26;
x_36 = x_41;
goto block_40;
}
else
{
lean_inc(x_34);
lean_dec(x_26);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_34);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_42 = lean_ctor_get(x_19, 0);
x_49 = !lean_is_exclusive(x_19);
if (x_49 == 0)
{
x_43 = x_19;
x_44 = x_49;
goto block_48;
}
else
{
lean_inc(x_42);
lean_dec(x_19);
x_43 = lean_box(0);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_44 == 0)
{
x_45 = x_43;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_42);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_50 = lean_ctor_get(x_15, 0);
x_57 = !lean_is_exclusive(x_15);
if (x_57 == 0)
{
x_51 = x_15;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_15);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_50);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__13_spec__17(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__13_spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__13_spec__17(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__13(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__13_spec__17(x_1, x_9, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__13(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__0));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__9));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__21));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__27(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__26));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__33(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__32));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_338 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__1));
x_339 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__0___redArg(x_338, x_8);
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
lean_dec_ref(x_339);
x_341 = lean_unbox(x_340);
lean_dec(x_340);
if (x_341 == 0)
{
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_9;
x_17 = lean_box(0);
goto block_337;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_342 = lean_ctor_get(x_1, 0);
x_343 = lean_ctor_get(x_342, 0);
x_344 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__33, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__33_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__33);
lean_inc(x_343);
x_345 = l_Lean_MessageData_ofName(x_343);
x_346 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_345);
x_347 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__138, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__138_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__138);
x_348 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
lean_inc_ref(x_2);
x_349 = lean_array_to_list(x_2);
x_350 = lean_box(0);
x_351 = l_List_mapTR_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__6(x_349, x_350);
x_352 = l_Lean_MessageData_ofList(x_351);
x_353 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_353, 0, x_348);
lean_ctor_set(x_353, 1, x_352);
x_354 = l_Lean_addTrace___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__7___redArg(x_338, x_353, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_354) == 0)
{
lean_dec_ref(x_354);
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_9;
x_17 = lean_box(0);
goto block_337;
}
else
{
lean_object* x_355; lean_object* x_356; uint8_t x_357; uint8_t x_362; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_355 = lean_ctor_get(x_354, 0);
x_362 = !lean_is_exclusive(x_354);
if (x_362 == 0)
{
x_356 = x_354;
x_357 = x_362;
goto block_361;
}
else
{
lean_inc(x_355);
lean_dec(x_354);
x_356 = lean_box(0);
x_357 = x_362;
goto block_361;
}
block_361:
{
lean_object* x_358; 
if (x_357 == 0)
{
x_358 = x_356;
goto block_359;
}
else
{
lean_object* x_360; 
x_360 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_360, 0, x_355);
x_358 = x_360;
goto block_359;
}
block_359:
{
return x_358;
}
}
}
}
block_337:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_1, 4);
lean_inc(x_19);
lean_dec_ref(x_1);
x_20 = lean_array_mk(x_19);
x_21 = lean_array_size(x_20);
x_22 = 0;
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc_ref(x_13);
x_23 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__12(x_2, x_21, x_22, x_20, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_328; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = l_Array_unzip___redArg(x_24);
lean_dec(x_24);
x_26 = lean_ctor_get(x_25, 0);
x_27 = lean_ctor_get(x_25, 1);
x_328 = !lean_is_exclusive(x_25);
if (x_328 == 0)
{
x_28 = x_25;
x_29 = x_328;
goto block_327;
}
else
{
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = x_328;
goto block_327;
}
block_327:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_326; 
x_30 = l_Array_unzip___redArg(x_27);
lean_dec(x_27);
x_31 = lean_ctor_get(x_30, 0);
x_32 = lean_ctor_get(x_30, 1);
x_326 = !lean_is_exclusive(x_30);
if (x_326 == 0)
{
x_33 = x_30;
x_34 = x_326;
goto block_325;
}
else
{
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_30);
x_33 = lean_box(0);
x_34 = x_326;
goto block_325;
}
block_325:
{
size_t x_35; lean_object* x_36; 
x_35 = lean_array_size(x_2);
x_36 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__2___redArg(x_35, x_22, x_2, x_13, x_15, x_16);
lean_dec(x_16);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_316; 
x_37 = lean_ctor_get(x_36, 0);
x_316 = !lean_is_exclusive(x_36);
if (x_316 == 0)
{
x_38 = x_36;
x_39 = x_316;
goto block_315;
}
else
{
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_box(0);
x_39 = x_316;
goto block_315;
}
block_315:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_312; 
x_40 = lean_ctor_get(x_15, 5);
lean_inc(x_40);
x_41 = lean_ctor_get(x_15, 10);
lean_inc(x_41);
x_42 = lean_ctor_get(x_15, 11);
lean_inc(x_42);
lean_dec_ref(x_15);
x_43 = lean_ctor_get(x_18, 0);
x_312 = !lean_is_exclusive(x_18);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_ctor_get(x_18, 2);
lean_dec(x_313);
x_314 = lean_ctor_get(x_18, 1);
lean_dec(x_314);
x_44 = x_18;
x_45 = x_312;
goto block_311;
}
else
{
lean_inc(x_43);
lean_dec(x_18);
x_44 = lean_box(0);
x_45 = x_312;
goto block_311;
}
block_311:
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18));
x_47 = 0;
x_48 = l_Lean_SourceInfo_fromRef(x_40, x_47);
lean_dec(x_40);
x_49 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__66));
x_50 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__67));
lean_inc(x_48);
if (x_34 == 0)
{
lean_ctor_set_tag(x_33, 2);
lean_ctor_set(x_33, 1, x_50);
lean_ctor_set(x_33, 0, x_48);
x_51 = x_33;
goto block_309;
}
else
{
lean_object* x_310; 
x_310 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_310, 0, x_48);
lean_ctor_set(x_310, 1, x_50);
x_51 = x_310;
goto block_309;
}
block_309:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = l_Lean_mkCIdent(x_43);
lean_inc(x_48);
x_53 = l_Lean_Syntax_node2(x_48, x_49, x_51, x_52);
x_54 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
x_55 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10);
x_56 = lean_array_size(x_37);
x_57 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__4(x_56, x_22, x_37);
x_58 = l_Array_append___redArg(x_55, x_57);
lean_dec_ref(x_57);
lean_inc(x_48);
if (x_45 == 0)
{
lean_ctor_set_tag(x_44, 1);
lean_ctor_set(x_44, 2, x_58);
lean_ctor_set(x_44, 1, x_54);
lean_ctor_set(x_44, 0, x_48);
x_59 = x_44;
goto block_307;
}
else
{
lean_object* x_308; 
x_308 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_308, 0, x_48);
lean_ctor_set(x_308, 1, x_54);
lean_ctor_set(x_308, 2, x_58);
x_59 = x_308;
goto block_307;
}
block_307:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_inc(x_48);
x_60 = l_Lean_Syntax_node2(x_48, x_46, x_53, x_59);
x_61 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__7));
x_62 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__9));
lean_inc(x_48);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_48);
lean_ctor_set(x_63, 1, x_54);
lean_ctor_set(x_63, 2, x_55);
lean_inc_ref_n(x_63, 7);
lean_inc(x_48);
x_64 = l_Lean_Syntax_node7(x_48, x_62, x_63, x_63, x_63, x_63, x_63, x_63, x_63);
x_65 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__0));
x_66 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__1));
lean_inc(x_48);
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 2);
lean_ctor_set(x_28, 1, x_65);
lean_ctor_set(x_28, 0, x_48);
x_67 = x_28;
goto block_305;
}
else
{
lean_object* x_306; 
x_306 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_306, 0, x_48);
lean_ctor_set(x_306, 1, x_65);
x_67 = x_306;
goto block_305;
}
block_305:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; size_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; size_t x_218; lean_object* x_219; size_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; size_t x_277; lean_object* x_278; size_t x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_68 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__15));
x_69 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__17, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__17_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__17);
x_70 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__18));
lean_inc(x_42);
lean_inc(x_41);
x_71 = l_Lean_addMacroScope(x_41, x_70, x_42);
x_72 = lean_box(0);
lean_inc(x_48);
x_73 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_73, 0, x_48);
lean_ctor_set(x_73, 1, x_69);
lean_ctor_set(x_73, 2, x_71);
lean_ctor_set(x_73, 3, x_72);
lean_inc_ref(x_63);
lean_inc_ref(x_73);
lean_inc(x_48);
x_74 = l_Lean_Syntax_node2(x_48, x_68, x_73, x_63);
x_75 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__6));
lean_inc_ref_n(x_63, 2);
lean_inc(x_48);
x_76 = l_Lean_Syntax_node2(x_48, x_75, x_63, x_63);
x_77 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__19));
lean_inc(x_48);
x_78 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_78, 0, x_48);
lean_ctor_set(x_78, 1, x_77);
lean_inc_ref(x_78);
lean_inc(x_48);
x_79 = l_Lean_Syntax_node1(x_48, x_54, x_78);
x_80 = lean_array_size(x_26);
x_81 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5(x_80, x_22, x_26);
x_82 = l_Array_append___redArg(x_55, x_81);
lean_dec_ref(x_81);
lean_inc(x_48);
x_83 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_83, 0, x_48);
lean_ctor_set(x_83, 1, x_54);
lean_ctor_set(x_83, 2, x_82);
x_84 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__23));
x_85 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__24));
lean_inc(x_48);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_48);
lean_ctor_set(x_86, 1, x_85);
x_87 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__26));
x_88 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__28, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__28_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__28);
x_89 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__29));
lean_inc(x_42);
lean_inc(x_41);
x_90 = l_Lean_addMacroScope(x_41, x_89, x_42);
x_91 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__34));
lean_inc(x_48);
x_92 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_92, 0, x_48);
lean_ctor_set(x_92, 1, x_88);
lean_ctor_set(x_92, 2, x_90);
lean_ctor_set(x_92, 3, x_91);
lean_inc_ref(x_63);
lean_inc(x_48);
x_93 = l_Lean_Syntax_node2(x_48, x_87, x_63, x_92);
x_94 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__35));
lean_inc(x_48);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_48);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__37, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__37_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__37);
x_97 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__38));
lean_inc(x_42);
lean_inc(x_41);
x_98 = l_Lean_addMacroScope(x_41, x_97, x_42);
x_99 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__43));
lean_inc(x_48);
x_100 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_100, 0, x_48);
lean_ctor_set(x_100, 1, x_96);
lean_ctor_set(x_100, 2, x_98);
lean_ctor_set(x_100, 3, x_99);
lean_inc_ref(x_63);
lean_inc(x_48);
x_101 = l_Lean_Syntax_node2(x_48, x_87, x_63, x_100);
lean_inc_ref(x_95);
lean_inc(x_48);
x_102 = l_Lean_Syntax_node3(x_48, x_54, x_93, x_95, x_101);
lean_inc(x_48);
x_103 = l_Lean_Syntax_node2(x_48, x_54, x_86, x_102);
lean_inc(x_48);
x_104 = l_Lean_Syntax_node1(x_48, x_84, x_103);
lean_inc_ref(x_63);
lean_inc(x_48);
x_105 = l_Lean_Syntax_node7(x_48, x_66, x_67, x_74, x_76, x_79, x_83, x_63, x_104);
lean_inc(x_48);
x_106 = l_Lean_Syntax_node2(x_48, x_61, x_64, x_105);
x_107 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__44));
x_108 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__45));
x_109 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__46));
x_110 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__47));
lean_inc(x_48);
x_111 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_111, 0, x_48);
lean_ctor_set(x_111, 1, x_109);
x_112 = l_Array_append___redArg(x_55, x_3);
lean_inc(x_48);
x_113 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_113, 0, x_48);
lean_ctor_set(x_113, 1, x_54);
lean_ctor_set(x_113, 2, x_112);
lean_inc(x_48);
x_114 = l_Lean_Syntax_node2(x_48, x_110, x_111, x_113);
lean_inc(x_48);
x_115 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_115, 0, x_48);
lean_ctor_set(x_115, 1, x_107);
x_116 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__2));
x_117 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__3));
lean_inc(x_48);
x_118 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_118, 0, x_48);
lean_ctor_set(x_118, 1, x_116);
lean_inc(x_48);
x_119 = l_Lean_Syntax_node1(x_48, x_117, x_118);
lean_inc(x_48);
x_120 = l_Lean_Syntax_node1(x_48, x_54, x_119);
lean_inc_ref_n(x_63, 6);
lean_inc(x_48);
x_121 = l_Lean_Syntax_node7(x_48, x_62, x_63, x_63, x_63, x_63, x_63, x_63, x_120);
x_122 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__48));
x_123 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__49));
x_124 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__51));
lean_inc_ref(x_63);
lean_inc(x_48);
x_125 = l_Lean_Syntax_node1(x_48, x_124, x_63);
lean_inc(x_48);
x_126 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_126, 0, x_48);
lean_ctor_set(x_126, 1, x_122);
x_127 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__53));
x_128 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__12));
x_129 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__13));
lean_inc(x_48);
x_130 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_130, 0, x_48);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__54, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__54_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__54);
x_132 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__55));
lean_inc(x_42);
lean_inc(x_41);
x_133 = l_Lean_addMacroScope(x_41, x_132, x_42);
x_134 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__58));
lean_inc(x_48);
x_135 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_135, 0, x_48);
lean_ctor_set(x_135, 1, x_131);
lean_ctor_set(x_135, 2, x_133);
lean_ctor_set(x_135, 3, x_134);
lean_inc(x_48);
x_136 = l_Lean_Syntax_node1(x_48, x_54, x_60);
lean_inc(x_48);
x_137 = l_Lean_Syntax_node2(x_48, x_46, x_135, x_136);
lean_inc_ref(x_130);
lean_inc(x_48);
x_138 = l_Lean_Syntax_node2(x_48, x_128, x_130, x_137);
lean_inc(x_138);
lean_inc_ref(x_63);
lean_inc(x_48);
x_139 = l_Lean_Syntax_node2(x_48, x_127, x_63, x_138);
x_140 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__69));
x_141 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__13));
lean_inc(x_48);
x_142 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_142, 0, x_48);
lean_ctor_set(x_142, 1, x_141);
x_143 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__71));
x_144 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__72));
lean_inc(x_48);
x_145 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_145, 0, x_48);
lean_ctor_set(x_145, 1, x_144);
x_146 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__74));
x_147 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__7));
x_148 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__9));
x_149 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__20);
x_150 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__21));
lean_inc(x_42);
lean_inc(x_41);
x_151 = l_Lean_addMacroScope(x_41, x_150, x_42);
x_152 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__76));
lean_inc(x_48);
x_153 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_153, 0, x_48);
lean_ctor_set(x_153, 1, x_149);
lean_ctor_set(x_153, 2, x_151);
lean_ctor_set(x_153, 3, x_152);
lean_inc_ref(x_63);
lean_inc(x_48);
x_154 = l_Lean_Syntax_node2(x_48, x_148, x_153, x_63);
x_155 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__12));
x_156 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__78, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__78_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__78);
x_157 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__79));
lean_inc(x_42);
lean_inc(x_41);
x_158 = l_Lean_addMacroScope(x_41, x_157, x_42);
lean_inc(x_48);
x_159 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_159, 0, x_48);
lean_ctor_set(x_159, 1, x_156);
lean_ctor_set(x_159, 2, x_158);
lean_ctor_set(x_159, 3, x_72);
lean_inc_ref(x_159);
lean_inc_ref(x_63);
lean_inc_ref(x_142);
lean_inc(x_48);
x_160 = l_Lean_Syntax_node3(x_48, x_155, x_142, x_63, x_159);
lean_inc_ref_n(x_63, 2);
lean_inc(x_48);
x_161 = l_Lean_Syntax_node3(x_48, x_54, x_63, x_63, x_160);
lean_inc(x_48);
x_162 = l_Lean_Syntax_node2(x_48, x_147, x_154, x_161);
x_163 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__36);
x_164 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__37));
lean_inc(x_42);
lean_inc(x_41);
x_165 = l_Lean_addMacroScope(x_41, x_164, x_42);
x_166 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__81));
lean_inc(x_48);
x_167 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_167, 0, x_48);
lean_ctor_set(x_167, 1, x_163);
lean_ctor_set(x_167, 2, x_165);
lean_ctor_set(x_167, 3, x_166);
lean_inc_ref(x_63);
lean_inc(x_48);
x_168 = l_Lean_Syntax_node2(x_48, x_148, x_167, x_63);
x_169 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__83, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__83_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__83);
x_170 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__84));
lean_inc(x_42);
lean_inc(x_41);
x_171 = l_Lean_addMacroScope(x_41, x_170, x_42);
lean_inc(x_48);
x_172 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_172, 0, x_48);
lean_ctor_set(x_172, 1, x_169);
lean_ctor_set(x_172, 2, x_171);
lean_ctor_set(x_172, 3, x_72);
lean_inc_ref(x_172);
lean_inc_ref(x_63);
lean_inc_ref(x_142);
lean_inc(x_48);
x_173 = l_Lean_Syntax_node3(x_48, x_155, x_142, x_63, x_172);
lean_inc_ref_n(x_63, 2);
lean_inc(x_48);
x_174 = l_Lean_Syntax_node3(x_48, x_54, x_63, x_63, x_173);
lean_inc(x_48);
x_175 = l_Lean_Syntax_node2(x_48, x_147, x_168, x_174);
lean_inc(x_48);
x_176 = l_Lean_Syntax_node3(x_48, x_54, x_162, x_95, x_175);
lean_inc(x_48);
x_177 = l_Lean_Syntax_node1(x_48, x_146, x_176);
x_178 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__86));
lean_inc_ref(x_63);
lean_inc(x_48);
x_179 = l_Lean_Syntax_node1(x_48, x_178, x_63);
x_180 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__87));
lean_inc(x_48);
x_181 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_181, 0, x_48);
lean_ctor_set(x_181, 1, x_180);
lean_inc_ref_n(x_63, 2);
lean_inc(x_48);
x_182 = l_Lean_Syntax_node6(x_48, x_143, x_145, x_63, x_177, x_179, x_63, x_181);
x_183 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__90));
lean_inc_ref_n(x_63, 2);
lean_inc(x_48);
x_184 = l_Lean_Syntax_node2(x_48, x_183, x_63, x_63);
x_185 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__92));
x_186 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__94));
x_187 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__96));
x_188 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__98));
x_189 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__100));
lean_inc(x_48);
x_190 = l_Lean_Syntax_node1(x_48, x_189, x_159);
x_191 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__4, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__4_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__4);
x_192 = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__0___redArg___closed__1));
lean_inc(x_42);
lean_inc(x_41);
x_193 = l_Lean_addMacroScope(x_41, x_192, x_42);
lean_inc(x_48);
x_194 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_194, 0, x_48);
lean_ctor_set(x_194, 1, x_191);
lean_ctor_set(x_194, 2, x_193);
lean_ctor_set(x_194, 3, x_72);
lean_inc_ref(x_194);
lean_inc(x_48);
x_195 = l_Lean_Syntax_node1(x_48, x_54, x_194);
x_196 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__5));
x_197 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__6));
lean_inc(x_48);
x_198 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_198, 0, x_48);
lean_ctor_set(x_198, 1, x_196);
x_199 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__8));
lean_inc_ref(x_63);
lean_inc(x_48);
x_200 = l_Lean_Syntax_node1(x_48, x_199, x_63);
x_201 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__10, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__10_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__10);
x_202 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__11));
lean_inc(x_42);
lean_inc(x_41);
x_203 = l_Lean_addMacroScope(x_41, x_202, x_42);
lean_inc(x_48);
x_204 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_204, 0, x_48);
lean_ctor_set(x_204, 1, x_201);
lean_ctor_set(x_204, 2, x_203);
lean_ctor_set(x_204, 3, x_72);
lean_inc(x_48);
x_205 = l_Lean_Syntax_node1(x_48, x_189, x_204);
lean_inc(x_48);
x_206 = l_Lean_Syntax_node1(x_48, x_54, x_138);
lean_inc(x_182);
lean_inc_ref(x_142);
lean_inc_ref(x_63);
lean_inc(x_48);
x_207 = l_Lean_Syntax_node5(x_48, x_188, x_205, x_63, x_206, x_142, x_182);
lean_inc(x_48);
x_208 = l_Lean_Syntax_node1(x_48, x_187, x_207);
x_209 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__12));
x_210 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__13));
lean_inc(x_48);
x_211 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_211, 0, x_48);
lean_ctor_set(x_211, 1, x_209);
x_212 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__15));
lean_inc_ref(x_63);
lean_inc(x_48);
x_213 = l_Lean_Syntax_node2(x_48, x_212, x_63, x_194);
lean_inc(x_48);
x_214 = l_Lean_Syntax_node1(x_48, x_54, x_213);
x_215 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__16));
lean_inc(x_48);
x_216 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_216, 0, x_48);
lean_ctor_set(x_216, 1, x_215);
x_217 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__18));
x_218 = lean_array_size(x_31);
x_219 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__13(x_218, x_22, x_31);
x_220 = lean_array_size(x_219);
x_221 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5(x_220, x_22, x_219);
x_222 = l_Array_append___redArg(x_55, x_221);
lean_dec_ref(x_221);
lean_inc(x_48);
x_223 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_223, 0, x_48);
lean_ctor_set(x_223, 1, x_54);
lean_ctor_set(x_223, 2, x_222);
lean_inc(x_48);
x_224 = l_Lean_Syntax_node1(x_48, x_217, x_223);
lean_inc_ref(x_216);
lean_inc_ref_n(x_63, 2);
lean_inc_ref(x_211);
lean_inc(x_48);
x_225 = l_Lean_Syntax_node6(x_48, x_210, x_211, x_63, x_63, x_214, x_216, x_224);
lean_inc_ref(x_63);
lean_inc(x_208);
lean_inc_ref(x_198);
lean_inc(x_48);
x_226 = l_Lean_Syntax_node5(x_48, x_197, x_198, x_200, x_208, x_63, x_225);
lean_inc_ref(x_142);
lean_inc_ref(x_63);
lean_inc(x_48);
x_227 = l_Lean_Syntax_node5(x_48, x_188, x_190, x_195, x_63, x_142, x_226);
lean_inc(x_48);
x_228 = l_Lean_Syntax_node1(x_48, x_187, x_227);
lean_inc(x_184);
lean_inc_ref_n(x_63, 2);
lean_inc(x_48);
x_229 = l_Lean_Syntax_node4(x_48, x_186, x_63, x_63, x_228, x_184);
lean_inc(x_48);
x_230 = l_Lean_Syntax_node1(x_48, x_189, x_172);
x_231 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__112, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__112_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__112);
x_232 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__113));
lean_inc(x_42);
lean_inc(x_41);
x_233 = l_Lean_addMacroScope(x_41, x_232, x_42);
lean_inc(x_48);
x_234 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_234, 0, x_48);
lean_ctor_set(x_234, 1, x_231);
lean_ctor_set(x_234, 2, x_233);
lean_ctor_set(x_234, 3, x_72);
lean_inc(x_48);
x_235 = l_Lean_Syntax_node1(x_48, x_54, x_234);
x_236 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__114));
x_237 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__115));
lean_inc(x_48);
x_238 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_238, 0, x_48);
lean_ctor_set(x_238, 1, x_236);
x_239 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__117));
x_240 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__119));
x_241 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__20));
lean_inc(x_48);
x_242 = l_Lean_Syntax_node2(x_48, x_241, x_198, x_208);
lean_inc_ref(x_63);
lean_inc(x_48);
x_243 = l_Lean_Syntax_node2(x_48, x_240, x_242, x_63);
x_244 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__121));
x_245 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__122));
lean_inc(x_48);
x_246 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_246, 0, x_48);
lean_ctor_set(x_246, 1, x_245);
x_247 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__124));
x_248 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__22, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__22_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__22);
x_249 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__23));
lean_inc(x_42);
lean_inc(x_41);
x_250 = l_Lean_addMacroScope(x_41, x_249, x_42);
lean_inc(x_48);
x_251 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_251, 0, x_48);
lean_ctor_set(x_251, 1, x_248);
lean_ctor_set(x_251, 2, x_250);
lean_ctor_set(x_251, 3, x_72);
lean_inc(x_48);
x_252 = l_Lean_Syntax_node2(x_48, x_128, x_130, x_73);
lean_inc(x_48);
x_253 = l_Lean_Syntax_node1(x_48, x_54, x_252);
x_254 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__16));
lean_inc(x_48);
x_255 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_255, 0, x_48);
lean_ctor_set(x_255, 1, x_254);
x_256 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__126));
x_257 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__128);
x_258 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__129));
lean_inc(x_42);
lean_inc(x_41);
x_259 = l_Lean_addMacroScope(x_41, x_258, x_42);
x_260 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__132));
lean_inc(x_48);
x_261 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_261, 0, x_48);
lean_ctor_set(x_261, 1, x_257);
lean_ctor_set(x_261, 2, x_259);
lean_ctor_set(x_261, 3, x_260);
lean_inc(x_235);
lean_inc(x_48);
x_262 = l_Lean_Syntax_node2(x_48, x_46, x_261, x_235);
lean_inc(x_48);
x_263 = l_Lean_Syntax_node1(x_48, x_256, x_262);
lean_inc_ref(x_251);
lean_inc(x_48);
x_264 = l_Lean_Syntax_node4(x_48, x_247, x_251, x_253, x_255, x_263);
lean_inc_ref(x_63);
lean_inc(x_48);
x_265 = l_Lean_Syntax_node3(x_48, x_244, x_246, x_63, x_264);
lean_inc_ref(x_63);
lean_inc(x_48);
x_266 = l_Lean_Syntax_node2(x_48, x_240, x_265, x_63);
x_267 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__25));
x_268 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__27, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__27_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__27);
x_269 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__28));
x_270 = l_Lean_addMacroScope(x_41, x_269, x_42);
x_271 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__30));
lean_inc(x_48);
x_272 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_272, 0, x_48);
lean_ctor_set(x_272, 1, x_268);
lean_ctor_set(x_272, 2, x_270);
lean_ctor_set(x_272, 3, x_271);
x_273 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___closed__31));
lean_inc(x_48);
x_274 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_274, 0, x_48);
lean_ctor_set(x_274, 1, x_273);
lean_inc_ref(x_63);
lean_inc(x_48);
x_275 = l_Lean_Syntax_node2(x_48, x_212, x_63, x_251);
lean_inc(x_48);
x_276 = l_Lean_Syntax_node1(x_48, x_54, x_275);
x_277 = lean_array_size(x_32);
x_278 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__13(x_277, x_22, x_32);
x_279 = lean_array_size(x_278);
x_280 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__5(x_279, x_22, x_278);
x_281 = l_Array_append___redArg(x_55, x_280);
lean_dec_ref(x_280);
lean_inc(x_48);
x_282 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_282, 0, x_48);
lean_ctor_set(x_282, 1, x_54);
lean_ctor_set(x_282, 2, x_281);
lean_inc(x_48);
x_283 = l_Lean_Syntax_node1(x_48, x_217, x_282);
lean_inc_ref_n(x_63, 2);
lean_inc(x_48);
x_284 = l_Lean_Syntax_node6(x_48, x_210, x_211, x_63, x_63, x_276, x_216, x_283);
lean_inc(x_48);
x_285 = l_Lean_Syntax_node3(x_48, x_267, x_272, x_274, x_284);
lean_inc(x_48);
x_286 = l_Lean_Syntax_node1(x_48, x_256, x_285);
lean_inc_ref(x_63);
lean_inc(x_48);
x_287 = l_Lean_Syntax_node2(x_48, x_240, x_286, x_63);
lean_inc(x_48);
x_288 = l_Lean_Syntax_node3(x_48, x_54, x_243, x_266, x_287);
lean_inc(x_48);
x_289 = l_Lean_Syntax_node1(x_48, x_239, x_288);
lean_inc(x_48);
x_290 = l_Lean_Syntax_node2(x_48, x_237, x_238, x_289);
lean_inc_ref(x_142);
lean_inc_ref(x_63);
lean_inc(x_48);
x_291 = l_Lean_Syntax_node5(x_48, x_188, x_230, x_235, x_63, x_142, x_290);
lean_inc(x_48);
x_292 = l_Lean_Syntax_node1(x_48, x_187, x_291);
lean_inc(x_184);
lean_inc_ref_n(x_63, 2);
lean_inc(x_48);
x_293 = l_Lean_Syntax_node4(x_48, x_186, x_63, x_63, x_292, x_184);
lean_inc_ref(x_63);
lean_inc(x_48);
x_294 = l_Lean_Syntax_node3(x_48, x_54, x_229, x_63, x_293);
lean_inc_ref(x_63);
lean_inc(x_48);
x_295 = l_Lean_Syntax_node3(x_48, x_185, x_78, x_294, x_63);
lean_inc(x_48);
x_296 = l_Lean_Syntax_node1(x_48, x_54, x_295);
lean_inc(x_48);
x_297 = l_Lean_Syntax_node4(x_48, x_140, x_142, x_182, x_184, x_296);
lean_inc_ref(x_63);
lean_inc(x_48);
x_298 = l_Lean_Syntax_node6(x_48, x_123, x_125, x_126, x_63, x_63, x_139, x_297);
lean_inc(x_48);
x_299 = l_Lean_Syntax_node2(x_48, x_61, x_121, x_298);
lean_inc(x_48);
x_300 = l_Lean_Syntax_node3(x_48, x_108, x_114, x_115, x_299);
x_301 = l_Lean_Syntax_node2(x_48, x_54, x_106, x_300);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_301);
x_302 = x_38;
goto block_303;
}
else
{
lean_object* x_304; 
x_304 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_304, 0, x_301);
x_302 = x_304;
goto block_303;
}
block_303:
{
return x_302;
}
}
}
}
}
}
}
else
{
lean_object* x_317; lean_object* x_318; uint8_t x_319; uint8_t x_324; 
lean_del_object(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_del_object(x_28);
lean_dec(x_26);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
x_317 = lean_ctor_get(x_36, 0);
x_324 = !lean_is_exclusive(x_36);
if (x_324 == 0)
{
x_318 = x_36;
x_319 = x_324;
goto block_323;
}
else
{
lean_inc(x_317);
lean_dec(x_36);
x_318 = lean_box(0);
x_319 = x_324;
goto block_323;
}
block_323:
{
lean_object* x_320; 
if (x_319 == 0)
{
x_320 = x_318;
goto block_321;
}
else
{
lean_object* x_322; 
x_322 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_322, 0, x_317);
x_320 = x_322;
goto block_321;
}
block_321:
{
return x_320;
}
}
}
}
}
}
else
{
lean_object* x_329; lean_object* x_330; uint8_t x_331; uint8_t x_336; 
lean_dec_ref(x_18);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_2);
x_329 = lean_ctor_get(x_23, 0);
x_336 = !lean_is_exclusive(x_23);
if (x_336 == 0)
{
x_330 = x_23;
x_331 = x_336;
goto block_335;
}
else
{
lean_inc(x_329);
lean_dec(x_23);
x_330 = lean_box(0);
x_331 = x_336;
goto block_335;
}
block_335:
{
lean_object* x_332; 
if (x_331 == 0)
{
x_332 = x_330;
goto block_333;
}
else
{
lean_object* x_334; 
x_334 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_334, 0, x_329);
x_332 = x_334;
goto block_333;
}
block_333:
{
return x_332;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___redArg(x_1, x_2, x_3, x_6, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___redArg(x_1, x_2, x_3, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__7_spec__7(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___redArg(x_1, x_2, x_3, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__8_spec__9(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg(x_1, x_2, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_11);
x_12 = l_Lean_Meta_isType(x_11, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_19 = lean_unbox(x_13);
lean_dec(x_13);
if (x_19 == 0)
{
x_14 = x_4;
goto block_18;
}
else
{
lean_object* x_20; 
lean_inc(x_11);
x_20 = lean_array_push(x_4, x_11);
x_14 = x_20;
goto block_18;
}
block_18:
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_14;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_21 = lean_ctor_get(x_12, 0);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
x_22 = x_12;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
else
{
lean_object* x_29; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_4);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___redArg(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget_borrowed(x_3, x_2);
lean_inc_ref(x_4);
x_11 = l_Lean_Meta_getFVarLocalDecl___redArg(x_10, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_ctor_get(x_5, 5);
x_14 = lean_ctor_get(x_5, 10);
x_15 = lean_ctor_get(x_5, 11);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = 0;
x_19 = l_Lean_SourceInfo_fromRef(x_13, x_18);
x_20 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__1));
x_21 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__2));
lean_inc(x_19);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__3___closed__4));
x_24 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__10);
lean_inc(x_19);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_24);
x_26 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__18));
x_27 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__54, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__54_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__54);
x_28 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__55));
lean_inc(x_15);
lean_inc(x_14);
x_29 = l_Lean_addMacroScope(x_14, x_28, x_15);
x_30 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__5));
lean_inc(x_19);
x_31 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set(x_31, 3, x_30);
x_32 = l_Lean_LocalDecl_userName(x_12);
lean_dec(x_12);
x_33 = lean_mk_syntax_ident(x_32);
lean_inc(x_19);
x_34 = l_Lean_Syntax_node1(x_19, x_23, x_33);
lean_inc(x_19);
x_35 = l_Lean_Syntax_node2(x_19, x_26, x_31, x_34);
x_36 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___closed__6));
lean_inc(x_19);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_19);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Syntax_node4(x_19, x_20, x_22, x_25, x_35, x_37);
x_39 = 1;
x_40 = lean_usize_add(x_2, x_39);
x_41 = lean_array_uset(x_17, x_2, x_38);
x_2 = x_40;
x_3 = x_41;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_43 = lean_ctor_get(x_11, 0);
x_50 = !lean_is_exclusive(x_11);
if (x_50 == 0)
{
x_44 = x_11;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_11);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg(x_8, x_9, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_37; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_array_get_size(x_4);
x_49 = lean_mk_empty_array_with_capacity(x_3);
x_50 = lean_nat_dec_lt(x_3, x_48);
if (x_50 == 0)
{
x_13 = x_49;
x_14 = lean_box(0);
goto block_36;
}
else
{
uint8_t x_51; 
x_51 = lean_nat_dec_le(x_48, x_48);
if (x_51 == 0)
{
if (x_50 == 0)
{
x_13 = x_49;
x_14 = lean_box(0);
goto block_36;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_48);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_54 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___redArg(x_4, x_52, x_53, x_49, x_8, x_9, x_10, x_11);
x_37 = x_54;
goto block_47;
}
}
else
{
size_t x_55; size_t x_56; lean_object* x_57; 
x_55 = 0;
x_56 = lean_usize_of_nat(x_48);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_57 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___redArg(x_4, x_55, x_56, x_49, x_8, x_9, x_10, x_11);
x_37 = x_57;
goto block_47;
}
}
block_36:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_array_size(x_13);
x_16 = 0;
lean_inc_ref(x_10);
lean_inc_ref(x_8);
x_17 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg(x_15, x_16, x_13, x_8, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_st_ref_get(x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_20);
lean_dec(x_19);
x_21 = l_Lean_isStructure(x_20, x_1);
if (x_21 == 0)
{
size_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_array_size(x_18);
x_23 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__2(x_22, x_16, x_18);
x_24 = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance(x_2, x_4, x_23, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_23);
return x_24;
}
else
{
size_t x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_array_size(x_18);
x_26 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__2(x_25, x_16, x_18);
x_27 = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance(x_2, x_4, x_26, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_28 = lean_ctor_get(x_17, 0);
x_35 = !lean_is_exclusive(x_17);
if (x_35 == 0)
{
x_29 = x_17;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
block_47:
{
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_13 = x_38;
x_14 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_39 = lean_ctor_get(x_37, 0);
x_46 = !lean_is_exclusive(x_37);
if (x_46 == 0)
{
x_40 = x_37;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_5);
lean_dec(x_3);
return x_13;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__4(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__3);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_usize(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__4);
x_3 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Elab_Command_instInhabitedScope_default;
x_9 = l_List_head_x21___redArg(x_8, x_7);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__2);
x_12 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___closed__5);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_10);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Elab_Command_instInhabitedScope_default;
x_8 = l_List_head_x21___redArg(x_7, x_6);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = l_Lean_Elab_pp_macroStack;
x_11 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__13(x_9, x_10);
lean_dec_ref(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_30; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_14, 0);
lean_dec(x_31);
x_16 = x_14;
x_17 = x_30;
goto block_29;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14___closed__0);
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_18);
lean_ctor_set(x_16, 0, x_1);
x_19 = x_16;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_18);
x_19 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11___redArg___closed__2);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_MessageData_ofSyntax(x_15);
x_23 = l_Lean_indentD(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__9_spec__11_spec__14(x_24, x_2);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg(x_1, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
lean_inc(x_7);
x_10 = l_Lean_Elab_getBetterRef(x_6, x_7);
lean_dec(x_6);
x_11 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___redArg(x_9, x_7, x_3);
x_12 = lean_ctor_get(x_11, 0);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
x_13 = x_11;
x_14 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_12);
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_5, 0);
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
x_22 = x_5;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_5);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
lean_inc(x_1);
x_7 = l_Lean_isInductiveCore_x3f(x_6, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__10___closed__1);
x_9 = 0;
x_10 = l_Lean_MessageData_ofConstName(x_1, x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_obj_once(&l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___closed__1);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg(x_13, x_2, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_15 = lean_ctor_get(x_7, 0);
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
x_16 = x_7;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 0);
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fget_borrowed(x_1, x_10);
lean_inc_ref(x_2);
lean_inc(x_11);
x_12 = l_Lean_getConstInfoInduct___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__0(x_11, x_2, x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_70; uint8_t x_71; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_13, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 3);
lean_inc(x_16);
lean_inc(x_11);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___lam__0___boxed), 12, 3);
lean_closure_set(x_17, 0, x_11);
lean_closure_set(x_17, 1, x_13);
lean_closure_set(x_17, 2, x_10);
x_70 = l_List_lengthTR___redArg(x_16);
lean_dec(x_16);
x_71 = lean_nat_dec_eq(x_70, x_6);
lean_dec(x_70);
if (x_71 == 0)
{
if (x_7 == 0)
{
x_55 = x_2;
x_56 = x_3;
x_57 = lean_box(0);
goto block_69;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_81; 
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec_ref(x_14);
x_72 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__3, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__3_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__3);
x_73 = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg(x_72, x_2, x_3);
lean_dec(x_3);
x_74 = lean_ctor_get(x_73, 0);
x_81 = !lean_is_exclusive(x_73);
if (x_81 == 0)
{
x_75 = x_73;
x_76 = x_81;
goto block_80;
}
else
{
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_box(0);
x_76 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_77; 
if (x_76 == 0)
{
x_77 = x_75;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_74);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
}
}
else
{
x_55 = x_2;
x_56 = x_3;
x_57 = lean_box(0);
goto block_69;
}
block_54:
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_14, 2);
lean_inc_ref(x_21);
lean_dec_ref(x_14);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_box(x_22);
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInductiveInstance_spec__11___boxed), 12, 5);
lean_closure_set(x_25, 0, lean_box(0));
lean_closure_set(x_25, 1, x_21);
lean_closure_set(x_25, 2, x_17);
lean_closure_set(x_25, 3, x_23);
lean_closure_set(x_25, 4, x_24);
lean_inc_ref(x_18);
x_26 = l_Lean_Elab_Command_liftTermElabM___redArg(x_25, x_18, x_19);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l_Lean_Elab_Command_elabCommand(x_27, x_18, x_19);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; uint8_t x_36; 
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_28, 0);
lean_dec(x_37);
x_29 = x_28;
x_30 = x_36;
goto block_35;
}
else
{
lean_dec(x_28);
x_29 = lean_box(0);
x_30 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(x_7);
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_31);
x_32 = x_29;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
x_38 = lean_ctor_get(x_28, 0);
x_45 = !lean_is_exclusive(x_28);
if (x_45 == 0)
{
x_39 = x_28;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_28);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_53; 
lean_dec(x_19);
lean_dec_ref(x_18);
x_46 = lean_ctor_get(x_26, 0);
x_53 = !lean_is_exclusive(x_26);
if (x_53 == 0)
{
x_47 = x_26;
x_48 = x_53;
goto block_52;
}
else
{
lean_inc(x_46);
lean_dec(x_26);
x_47 = lean_box(0);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_48 == 0)
{
x_49 = x_47;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_46);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
block_69:
{
uint8_t x_58; 
x_58 = lean_nat_dec_eq(x_15, x_10);
lean_dec(x_15);
if (x_58 == 0)
{
if (x_7 == 0)
{
x_18 = x_55;
x_19 = x_56;
x_20 = lean_box(0);
goto block_54;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_68; 
lean_dec_ref(x_17);
lean_dec_ref(x_14);
x_59 = lean_obj_once(&l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__1, &l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__1_once, _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___closed__1);
x_60 = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg(x_59, x_55, x_56);
lean_dec(x_56);
x_61 = lean_ctor_get(x_60, 0);
x_68 = !lean_is_exclusive(x_60);
if (x_68 == 0)
{
x_62 = x_60;
x_63 = x_68;
goto block_67;
}
else
{
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_box(0);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
if (x_63 == 0)
{
x_64 = x_62;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_61);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
}
}
else
{
x_18 = x_55;
x_19 = x_56;
x_20 = lean_box(0);
goto block_54;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_89; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_82 = lean_ctor_get(x_12, 0);
x_89 = !lean_is_exclusive(x_12);
if (x_89 == 0)
{
x_83 = x_12;
x_84 = x_89;
goto block_88;
}
else
{
lean_inc(x_82);
lean_dec(x_12);
x_83 = lean_box(0);
x_84 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_85; 
if (x_84 == 0)
{
x_85 = x_83;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_82);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___redArg(x_1, x_2, x_3, x_6, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__3(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__4(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveInstance_spec__4_spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RpcEncodable_initFn_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance_spec__1___closed__57));
x_3 = ((lean_object*)(l_Lean_Server_RpcEncodable_initFn___closed__0_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_));
x_4 = l_Lean_Elab_registerDerivingHandler(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_4);
x_5 = ((lean_object*)(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_deriveStructureInstance___closed__1));
x_6 = 0;
x_7 = ((lean_object*)(l_Lean_Server_RpcEncodable_initFn___closed__18_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_));
x_8 = l_Lean_registerTraceClass(x_5, x_6, x_7);
return x_8;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RpcEncodable_initFn_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_RpcEncodable_initFn_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Rpc_Deriving(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Deriving_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Server_RpcEncodable_initFn_00___x40_Lean_Server_Rpc_Deriving_198155338____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_Rpc_Deriving(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm = _init_l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm();
lean_mark_persistent(l___private_Lean_Server_Rpc_Deriving_0__Lean_Server_RpcEncodable_matchAltTerm);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Rpc_Deriving(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Deriving_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Rpc_Deriving(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_Rpc_Deriving(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_Rpc_Deriving(builtin);
}
#ifdef __cplusplus
}
#endif
