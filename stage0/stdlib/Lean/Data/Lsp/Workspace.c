// Lean compiler output
// Module: Lean.Data.Lsp.Workspace
// Imports: public import Lean.Data.Lsp.Basic
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
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "uri"};
static const lean_object* l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1_value;
static const lean_array_object l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkspaceFolder_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonWorkspaceFolder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonWorkspaceFolder_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonWorkspaceFolder___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceFolder___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonWorkspaceFolder = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceFolder___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Lsp"};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "WorkspaceFolder"};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 202, 85, 200, 38, 26, 140, 92)}};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4;
static const lean_string_object l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(102, 169, 49, 149, 57, 117, 3, 84)}};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__7_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__9;
static const lean_string_object l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__11;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__12 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__12_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__13;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__14;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonWorkspaceFolder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder___closed__0_value;
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "globPattern"};
static const lean_object* l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "FileSystemWatcher"};
static const lean_object* l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(188, 187, 45, 21, 24, 130, 104, 243)}};
static const lean_object* l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4;
static const lean_ctor_object l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(14, 132, 73, 204, 200, 87, 59, 188)}};
static const lean_object* l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8;
static const lean_string_object l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "kind"};
static const lean_object* l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__9_value;
static const lean_string_object l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "kind\?"};
static const lean_object* l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__10_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__10_value),LEAN_SCALAR_PTR_LITERAL(234, 251, 71, 75, 78, 98, 206, 187)}};
static const lean_object* l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__11 = (const lean_object*)&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__11_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13;
static lean_once_cell_t l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonFileSystemWatcher___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonFileSystemWatcher___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonFileSystemWatcher___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonFileSystemWatcher = (const lean_object*)&l_Lean_Lsp_instFromJsonFileSystemWatcher___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonFileSystemWatcher_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileSystemWatcher_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonFileSystemWatcher___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonFileSystemWatcher_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonFileSystemWatcher___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonFileSystemWatcher___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonFileSystemWatcher = (const lean_object*)&l_Lean_Lsp_instToJsonFileSystemWatcher___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_FileSystemWatcher_create;
LEAN_EXPORT lean_object* l_Lean_Lsp_FileSystemWatcher_change;
LEAN_EXPORT lean_object* l_Lean_Lsp_FileSystemWatcher_delete;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "watchers"};
static const lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "DidChangeWatchedFilesRegistrationOptions"};
static const lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 96, 16, 106, 210, 142, 61, 216)}};
static const lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 74, 50, 33, 192, 189, 4, 144)}};
static const lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions = (const lean_object*)&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions = (const lean_object*)&l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Created_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Created_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Created_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Created_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Changed_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Changed_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Changed_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Changed_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Deleted_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Deleted_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Deleted_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Deleted_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "expected 1, 2, or 3, got "};
static const lean_object* l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonFileChangeType___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonFileChangeType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonFileChangeType___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonFileChangeType___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonFileChangeType___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonFileChangeType = (const lean_object*)&l_Lean_Lsp_instFromJsonFileChangeType___closed__0_value;
static lean_once_cell_t l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0;
static lean_once_cell_t l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1;
static lean_once_cell_t l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2;
static lean_once_cell_t l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3;
static lean_once_cell_t l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4;
static lean_once_cell_t l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileChangeType___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileChangeType___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonFileChangeType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonFileChangeType___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonFileChangeType___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonFileChangeType___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonFileChangeType = (const lean_object*)&l_Lean_Lsp_instToJsonFileChangeType___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "FileEvent"};
static const lean_object* l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 156, 121, 219, 160, 108, 5, 208)}};
static const lean_object* l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5;
static const lean_string_object l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6_value),LEAN_SCALAR_PTR_LITERAL(112, 109, 54, 158, 248, 169, 165, 159)}};
static const lean_object* l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__7_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonFileEvent_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonFileEvent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonFileEvent_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonFileEvent___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonFileEvent___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonFileEvent = (const lean_object*)&l_Lean_Lsp_instFromJsonFileEvent___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileEvent_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileEvent_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonFileEvent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonFileEvent_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonFileEvent___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonFileEvent___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonFileEvent = (const lean_object*)&l_Lean_Lsp_instToJsonFileEvent___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "changes"};
static const lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "DidChangeWatchedFilesParams"};
static const lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(39, 8, 46, 178, 123, 139, 152, 5)}};
static const lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(203, 36, 97, 89, 231, 237, 32, 10)}};
static const lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams = (const lean_object*)&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams = (const lean_object*)&l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(lean_object* v_a_1_, lean_object* v_a_2_){
_start:
{
if (lean_obj_tag(v_a_1_) == 0)
{
lean_object* v___x_3_; 
v___x_3_ = lean_array_to_list(v_a_2_);
return v___x_3_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; lean_object* v___x_6_; 
v_head_4_ = lean_ctor_get(v_a_1_, 0);
lean_inc(v_head_4_);
v_tail_5_ = lean_ctor_get(v_a_1_, 1);
lean_inc(v_tail_5_);
lean_dec_ref(v_a_1_);
v___x_6_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2_, v_head_4_);
v_a_1_ = v_tail_5_;
v_a_2_ = v___x_6_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkspaceFolder_toJson(lean_object* v_x_12_){
_start:
{
lean_object* v_uri_13_; lean_object* v_name_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_34_; 
v_uri_13_ = lean_ctor_get(v_x_12_, 0);
v_name_14_ = lean_ctor_get(v_x_12_, 1);
v_isSharedCheck_34_ = !lean_is_exclusive(v_x_12_);
if (v_isSharedCheck_34_ == 0)
{
v___x_16_ = v_x_12_;
v_isShared_17_ = v_isSharedCheck_34_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_name_14_);
lean_inc(v_uri_13_);
lean_dec(v_x_12_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_34_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_21_; 
v___x_18_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0));
v___x_19_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_19_, 0, v_uri_13_);
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 1, v___x_19_);
lean_ctor_set(v___x_16_, 0, v___x_18_);
v___x_21_ = v___x_16_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v___x_18_);
lean_ctor_set(v_reuseFailAlloc_33_, 1, v___x_19_);
v___x_21_ = v_reuseFailAlloc_33_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_22_ = lean_box(0);
v___x_23_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_23_, 0, v___x_21_);
lean_ctor_set(v___x_23_, 1, v___x_22_);
v___x_24_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1));
v___x_25_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_25_, 0, v_name_14_);
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v___x_24_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
v___x_27_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
lean_ctor_set(v___x_27_, 1, v___x_22_);
v___x_28_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
lean_ctor_set(v___x_28_, 1, v___x_22_);
v___x_29_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_23_);
lean_ctor_set(v___x_29_, 1, v___x_28_);
v___x_30_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2));
v___x_31_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(v___x_29_, v___x_30_);
v___x_32_ = l_Lean_Json_mkObj(v___x_31_);
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(lean_object* v_j_37_, lean_object* v_k_38_){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = l_Lean_Json_getObjValD(v_j_37_, v_k_38_);
v___x_40_ = l_Lean_Json_getStr_x3f(v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0___boxed(lean_object* v_j_41_, lean_object* v_k_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(v_j_41_, v_k_42_);
lean_dec_ref(v_k_42_);
return v_res_43_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4(void){
_start:
{
uint8_t v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = 1;
v___x_52_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3));
v___x_53_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5));
v___x_56_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4);
v___x_57_ = lean_string_append(v___x_56_, v___x_55_);
return v___x_57_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8(void){
_start:
{
uint8_t v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = 1;
v___x_61_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__7));
v___x_62_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_61_, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__9(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8);
v___x_64_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6);
v___x_65_ = lean_string_append(v___x_64_, v___x_63_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__11(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
v___x_68_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__9, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__9);
v___x_69_ = lean_string_append(v___x_68_, v___x_67_);
return v___x_69_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__13(void){
_start:
{
uint8_t v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = 1;
v___x_73_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__12));
v___x_74_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_73_, v___x_72_);
return v___x_74_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__14(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_75_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__13, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__13);
v___x_76_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6);
v___x_77_ = lean_string_append(v___x_76_, v___x_75_);
return v___x_77_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
v___x_79_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__14, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__14);
v___x_80_ = lean_string_append(v___x_79_, v___x_78_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson(lean_object* v_json_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0));
lean_inc(v_json_81_);
v___x_83_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(v_json_81_, v___x_82_);
if (lean_obj_tag(v___x_83_) == 0)
{
lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_93_; 
lean_dec(v_json_81_);
v_a_84_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_93_ == 0)
{
v___x_86_ = v___x_83_;
v_isShared_87_ = v_isSharedCheck_93_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v___x_83_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_93_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_91_; 
v___x_88_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__11, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__11);
v___x_89_ = lean_string_append(v___x_88_, v_a_84_);
lean_dec(v_a_84_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 0, v___x_89_);
v___x_91_ = v___x_86_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_89_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
else
{
if (lean_obj_tag(v___x_83_) == 0)
{
lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_101_; 
lean_dec(v_json_81_);
v_a_94_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_101_ == 0)
{
v___x_96_ = v___x_83_;
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___x_83_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set_tag(v___x_96_, 0);
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_a_94_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_a_102_ = lean_ctor_get(v___x_83_, 0);
lean_inc(v_a_102_);
lean_dec_ref(v___x_83_);
v___x_103_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1));
v___x_104_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(v_json_81_, v___x_103_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_114_; 
lean_dec(v_a_102_);
v_a_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_114_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_114_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_114_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_112_; 
v___x_109_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15);
v___x_110_ = lean_string_append(v___x_109_, v_a_105_);
lean_dec(v_a_105_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v___x_110_);
v___x_112_ = v___x_107_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_110_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
else
{
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
lean_dec(v_a_102_);
v_a_115_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v___x_104_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_104_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
lean_ctor_set_tag(v___x_117_, 0);
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
else
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_131_; 
v_a_123_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_131_ == 0)
{
v___x_125_ = v___x_104_;
v_isShared_126_ = v_isSharedCheck_131_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_104_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_131_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v_a_102_);
lean_ctor_set(v___x_127_, 1, v_a_123_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_127_);
v___x_129_ = v___x_125_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0(lean_object* v_x_136_){
_start:
{
if (lean_obj_tag(v_x_136_) == 0)
{
lean_object* v___x_137_; 
v___x_137_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0___closed__0));
return v___x_137_;
}
else
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Json_getNat_x3f(v_x_136_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_138_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_155_; 
v_a_147_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_155_ == 0)
{
v___x_149_ = v___x_138_;
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_138_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_151_, 0, v_a_147_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_151_);
v___x_153_ = v___x_149_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0(lean_object* v_j_156_, lean_object* v_k_157_){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = l_Lean_Json_getObjValD(v_j_156_, v_k_157_);
v___x_159_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0(v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0___boxed(lean_object* v_j_160_, lean_object* v_k_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0(v_j_160_, v_k_161_);
lean_dec_ref(v_k_161_);
return v_res_162_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3(void){
_start:
{
uint8_t v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = 1;
v___x_170_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2));
v___x_171_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_170_, v___x_169_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5));
v___x_173_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3);
v___x_174_ = lean_string_append(v___x_173_, v___x_172_);
return v___x_174_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6(void){
_start:
{
uint8_t v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = 1;
v___x_178_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__5));
v___x_179_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_178_, v___x_177_);
return v___x_179_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6);
v___x_181_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4);
v___x_182_ = lean_string_append(v___x_181_, v___x_180_);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
v___x_184_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7);
v___x_185_ = lean_string_append(v___x_184_, v___x_183_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12(void){
_start:
{
uint8_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = 1;
v___x_191_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__11));
v___x_192_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_191_, v___x_190_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12);
v___x_194_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4);
v___x_195_ = lean_string_append(v___x_194_, v___x_193_);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
v___x_197_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13);
v___x_198_ = lean_string_append(v___x_197_, v___x_196_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson(lean_object* v_json_199_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__0));
lean_inc(v_json_199_);
v___x_201_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(v_json_199_, v___x_200_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_211_; 
lean_dec(v_json_199_);
v_a_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_211_ == 0)
{
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_211_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_211_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_206_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8);
v___x_207_ = lean_string_append(v___x_206_, v_a_202_);
lean_dec(v_a_202_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_207_);
v___x_209_ = v___x_204_;
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
else
{
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
lean_dec(v_json_199_);
v_a_212_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v___x_201_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_201_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
lean_ctor_set_tag(v___x_214_, 0);
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
else
{
lean_object* v_a_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_a_220_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_a_220_);
lean_dec_ref(v___x_201_);
v___x_221_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__9));
v___x_222_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0(v_json_199_, v___x_221_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_232_; 
lean_dec(v_a_220_);
v_a_223_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_232_ == 0)
{
v___x_225_ = v___x_222_;
v_isShared_226_ = v_isSharedCheck_232_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_222_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_232_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_227_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14);
v___x_228_ = lean_string_append(v___x_227_, v_a_223_);
lean_dec(v_a_223_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v___x_228_);
v___x_230_ = v___x_225_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
else
{
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
lean_dec(v_a_220_);
v_a_233_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_222_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_222_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set_tag(v___x_235_, 0);
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
else
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_249_; 
v_a_241_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_249_ == 0)
{
v___x_243_ = v___x_222_;
v_isShared_244_ = v_isSharedCheck_249_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_222_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_249_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v_a_220_);
lean_ctor_set(v___x_245_, 1, v_a_241_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_245_);
v___x_247_ = v___x_243_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonFileSystemWatcher_toJson_spec__0(lean_object* v_k_252_, lean_object* v_x_253_){
_start:
{
if (lean_obj_tag(v_x_253_) == 0)
{
lean_object* v___x_254_; 
lean_dec_ref(v_k_252_);
v___x_254_ = lean_box(0);
return v___x_254_;
}
else
{
lean_object* v_val_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_266_; 
v_val_255_ = lean_ctor_get(v_x_253_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v_x_253_);
if (v_isSharedCheck_266_ == 0)
{
v___x_257_ = v_x_253_;
v_isShared_258_ = v_isSharedCheck_266_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_val_255_);
lean_dec(v_x_253_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_266_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_259_ = l_Lean_JsonNumber_fromNat(v_val_255_);
if (v_isShared_258_ == 0)
{
lean_ctor_set_tag(v___x_257_, 2);
lean_ctor_set(v___x_257_, 0, v___x_259_);
v___x_261_ = v___x_257_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_265_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v_k_252_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = lean_box(0);
v___x_264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_262_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
return v___x_264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileSystemWatcher_toJson(lean_object* v_x_267_){
_start:
{
lean_object* v_globPattern_268_; lean_object* v_kind_x3f_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_287_; 
v_globPattern_268_ = lean_ctor_get(v_x_267_, 0);
v_kind_x3f_269_ = lean_ctor_get(v_x_267_, 1);
v_isSharedCheck_287_ = !lean_is_exclusive(v_x_267_);
if (v_isSharedCheck_287_ == 0)
{
v___x_271_ = v_x_267_;
v_isShared_272_ = v_isSharedCheck_287_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_kind_x3f_269_);
lean_inc(v_globPattern_268_);
lean_dec(v_x_267_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_287_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_273_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__0));
v___x_274_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_274_, 0, v_globPattern_268_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 1, v___x_274_);
lean_ctor_set(v___x_271_, 0, v___x_273_);
v___x_276_ = v___x_271_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v___x_274_);
v___x_276_ = v_reuseFailAlloc_286_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_277_ = lean_box(0);
v___x_278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_276_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__9));
v___x_280_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonFileSystemWatcher_toJson_spec__0(v___x_279_, v_kind_x3f_269_);
v___x_281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v___x_277_);
v___x_282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_278_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2));
v___x_284_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(v___x_282_, v___x_283_);
v___x_285_ = l_Lean_Json_mkObj(v___x_284_);
return v___x_285_;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_FileSystemWatcher_create(void){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = lean_unsigned_to_nat(1u);
return v___x_290_;
}
}
static lean_object* _init_l_Lean_Lsp_FileSystemWatcher_change(void){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = lean_unsigned_to_nat(2u);
return v___x_291_;
}
}
static lean_object* _init_l_Lean_Lsp_FileSystemWatcher_delete(void){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = lean_unsigned_to_nat(4u);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1(size_t v_sz_293_, size_t v_i_294_, lean_object* v_bs_295_){
_start:
{
uint8_t v___x_296_; 
v___x_296_ = lean_usize_dec_lt(v_i_294_, v_sz_293_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
v___x_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_297_, 0, v_bs_295_);
return v___x_297_;
}
else
{
lean_object* v_v_298_; lean_object* v___x_299_; 
v_v_298_ = lean_array_uget_borrowed(v_bs_295_, v_i_294_);
lean_inc(v_v_298_);
v___x_299_ = l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson(v_v_298_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec_ref(v_bs_295_);
v_a_300_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_299_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_299_);
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
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_308_; lean_object* v___x_309_; lean_object* v_bs_x27_310_; size_t v___x_311_; size_t v___x_312_; lean_object* v___x_313_; 
v_a_308_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_308_);
lean_dec_ref(v___x_299_);
v___x_309_ = lean_unsigned_to_nat(0u);
v_bs_x27_310_ = lean_array_uset(v_bs_295_, v_i_294_, v___x_309_);
v___x_311_ = ((size_t)1ULL);
v___x_312_ = lean_usize_add(v_i_294_, v___x_311_);
v___x_313_ = lean_array_uset(v_bs_x27_310_, v_i_294_, v_a_308_);
v_i_294_ = v___x_312_;
v_bs_295_ = v___x_313_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_315_, lean_object* v_i_316_, lean_object* v_bs_317_){
_start:
{
size_t v_sz_boxed_318_; size_t v_i_boxed_319_; lean_object* v_res_320_; 
v_sz_boxed_318_ = lean_unbox_usize(v_sz_315_);
lean_dec(v_sz_315_);
v_i_boxed_319_ = lean_unbox_usize(v_i_316_);
lean_dec(v_i_316_);
v_res_320_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_318_, v_i_boxed_319_, v_bs_317_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0(lean_object* v_x_323_){
_start:
{
if (lean_obj_tag(v_x_323_) == 4)
{
lean_object* v_elems_324_; size_t v_sz_325_; size_t v___x_326_; lean_object* v___x_327_; 
v_elems_324_ = lean_ctor_get(v_x_323_, 0);
lean_inc_ref(v_elems_324_);
lean_dec_ref(v_x_323_);
v_sz_325_ = lean_array_size(v_elems_324_);
v___x_326_ = ((size_t)0ULL);
v___x_327_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1(v_sz_325_, v___x_326_, v_elems_324_);
return v___x_327_;
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_328_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0));
v___x_329_ = lean_unsigned_to_nat(80u);
v___x_330_ = l_Lean_Json_pretty(v_x_323_, v___x_329_);
v___x_331_ = lean_string_append(v___x_328_, v___x_330_);
lean_dec_ref(v___x_330_);
v___x_332_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1));
v___x_333_ = lean_string_append(v___x_331_, v___x_332_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0(lean_object* v_j_335_, lean_object* v_k_336_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = l_Lean_Json_getObjValD(v_j_335_, v_k_336_);
v___x_338_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0(v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0___boxed(lean_object* v_j_339_, lean_object* v_k_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0(v_j_339_, v_k_340_);
lean_dec_ref(v_k_340_);
return v_res_341_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3(void){
_start:
{
uint8_t v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = 1;
v___x_349_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2));
v___x_350_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_349_, v___x_348_);
return v___x_350_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_351_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5));
v___x_352_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3);
v___x_353_ = lean_string_append(v___x_352_, v___x_351_);
return v___x_353_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6(void){
_start:
{
uint8_t v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = 1;
v___x_357_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__5));
v___x_358_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_357_, v___x_356_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6);
v___x_360_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4);
v___x_361_ = lean_string_append(v___x_360_, v___x_359_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
v___x_363_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7);
v___x_364_ = lean_string_append(v___x_363_, v___x_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson(lean_object* v_json_365_){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0));
v___x_367_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0(v_json_365_, v___x_366_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_377_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_377_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_377_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_377_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_372_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8);
v___x_373_ = lean_string_append(v___x_372_, v_a_368_);
lean_dec(v_a_368_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_373_);
v___x_375_ = v___x_370_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_385_; 
v_a_378_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_385_ == 0)
{
v___x_380_ = v___x_367_;
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_367_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
if (v_isShared_381_ == 0)
{
lean_ctor_set_tag(v___x_380_, 0);
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_a_378_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
v_a_386_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_367_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_367_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0(size_t v_sz_396_, size_t v_i_397_, lean_object* v_bs_398_){
_start:
{
uint8_t v___x_399_; 
v___x_399_ = lean_usize_dec_lt(v_i_397_, v_sz_396_);
if (v___x_399_ == 0)
{
return v_bs_398_;
}
else
{
lean_object* v_v_400_; lean_object* v___x_401_; lean_object* v_bs_x27_402_; lean_object* v___x_403_; size_t v___x_404_; size_t v___x_405_; lean_object* v___x_406_; 
v_v_400_ = lean_array_uget(v_bs_398_, v_i_397_);
v___x_401_ = lean_unsigned_to_nat(0u);
v_bs_x27_402_ = lean_array_uset(v_bs_398_, v_i_397_, v___x_401_);
v___x_403_ = l_Lean_Lsp_instToJsonFileSystemWatcher_toJson(v_v_400_);
v___x_404_ = ((size_t)1ULL);
v___x_405_ = lean_usize_add(v_i_397_, v___x_404_);
v___x_406_ = lean_array_uset(v_bs_x27_402_, v_i_397_, v___x_403_);
v_i_397_ = v___x_405_;
v_bs_398_ = v___x_406_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0___boxed(lean_object* v_sz_408_, lean_object* v_i_409_, lean_object* v_bs_410_){
_start:
{
size_t v_sz_boxed_411_; size_t v_i_boxed_412_; lean_object* v_res_413_; 
v_sz_boxed_411_ = lean_unbox_usize(v_sz_408_);
lean_dec(v_sz_408_);
v_i_boxed_412_ = lean_unbox_usize(v_i_409_);
lean_dec(v_i_409_);
v_res_413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0(v_sz_boxed_411_, v_i_boxed_412_, v_bs_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0(lean_object* v_a_414_){
_start:
{
size_t v_sz_415_; size_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_sz_415_ = lean_array_size(v_a_414_);
v___x_416_ = ((size_t)0ULL);
v___x_417_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0(v_sz_415_, v___x_416_, v_a_414_);
v___x_418_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson(lean_object* v_x_419_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_420_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0));
v___x_421_ = l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0(v_x_419_);
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_420_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = lean_box(0);
v___x_424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_422_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v___x_423_);
v___x_426_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2));
v___x_427_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(v___x_425_, v___x_426_);
v___x_428_ = l_Lean_Json_mkObj(v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorIdx(uint8_t v_x_431_){
_start:
{
switch(v_x_431_)
{
case 0:
{
lean_object* v___x_432_; 
v___x_432_ = lean_unsigned_to_nat(0u);
return v___x_432_;
}
case 1:
{
lean_object* v___x_433_; 
v___x_433_ = lean_unsigned_to_nat(1u);
return v___x_433_;
}
default: 
{
lean_object* v___x_434_; 
v___x_434_ = lean_unsigned_to_nat(2u);
return v___x_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorIdx___boxed(lean_object* v_x_435_){
_start:
{
uint8_t v_x_boxed_436_; lean_object* v_res_437_; 
v_x_boxed_436_ = lean_unbox(v_x_435_);
v_res_437_ = l_Lean_Lsp_FileChangeType_ctorIdx(v_x_boxed_436_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_toCtorIdx(uint8_t v_x_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Lsp_FileChangeType_ctorIdx(v_x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_toCtorIdx___boxed(lean_object* v_x_440_){
_start:
{
uint8_t v_x_4__boxed_441_; lean_object* v_res_442_; 
v_x_4__boxed_441_ = lean_unbox(v_x_440_);
v_res_442_ = l_Lean_Lsp_FileChangeType_toCtorIdx(v_x_4__boxed_441_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorElim___redArg(lean_object* v_k_443_){
_start:
{
lean_inc(v_k_443_);
return v_k_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorElim___redArg___boxed(lean_object* v_k_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Lsp_FileChangeType_ctorElim___redArg(v_k_444_);
lean_dec(v_k_444_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorElim(lean_object* v_motive_446_, lean_object* v_ctorIdx_447_, uint8_t v_t_448_, lean_object* v_h_449_, lean_object* v_k_450_){
_start:
{
lean_inc(v_k_450_);
return v_k_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorElim___boxed(lean_object* v_motive_451_, lean_object* v_ctorIdx_452_, lean_object* v_t_453_, lean_object* v_h_454_, lean_object* v_k_455_){
_start:
{
uint8_t v_t_boxed_456_; lean_object* v_res_457_; 
v_t_boxed_456_ = lean_unbox(v_t_453_);
v_res_457_ = l_Lean_Lsp_FileChangeType_ctorElim(v_motive_451_, v_ctorIdx_452_, v_t_boxed_456_, v_h_454_, v_k_455_);
lean_dec(v_k_455_);
lean_dec(v_ctorIdx_452_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Created_elim___redArg(lean_object* v_Created_458_){
_start:
{
lean_inc(v_Created_458_);
return v_Created_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Created_elim___redArg___boxed(lean_object* v_Created_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_Lsp_FileChangeType_Created_elim___redArg(v_Created_459_);
lean_dec(v_Created_459_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Created_elim(lean_object* v_motive_461_, uint8_t v_t_462_, lean_object* v_h_463_, lean_object* v_Created_464_){
_start:
{
lean_inc(v_Created_464_);
return v_Created_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Created_elim___boxed(lean_object* v_motive_465_, lean_object* v_t_466_, lean_object* v_h_467_, lean_object* v_Created_468_){
_start:
{
uint8_t v_t_boxed_469_; lean_object* v_res_470_; 
v_t_boxed_469_ = lean_unbox(v_t_466_);
v_res_470_ = l_Lean_Lsp_FileChangeType_Created_elim(v_motive_465_, v_t_boxed_469_, v_h_467_, v_Created_468_);
lean_dec(v_Created_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Changed_elim___redArg(lean_object* v_Changed_471_){
_start:
{
lean_inc(v_Changed_471_);
return v_Changed_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Changed_elim___redArg___boxed(lean_object* v_Changed_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Lsp_FileChangeType_Changed_elim___redArg(v_Changed_472_);
lean_dec(v_Changed_472_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Changed_elim(lean_object* v_motive_474_, uint8_t v_t_475_, lean_object* v_h_476_, lean_object* v_Changed_477_){
_start:
{
lean_inc(v_Changed_477_);
return v_Changed_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Changed_elim___boxed(lean_object* v_motive_478_, lean_object* v_t_479_, lean_object* v_h_480_, lean_object* v_Changed_481_){
_start:
{
uint8_t v_t_boxed_482_; lean_object* v_res_483_; 
v_t_boxed_482_ = lean_unbox(v_t_479_);
v_res_483_ = l_Lean_Lsp_FileChangeType_Changed_elim(v_motive_478_, v_t_boxed_482_, v_h_480_, v_Changed_481_);
lean_dec(v_Changed_481_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Deleted_elim___redArg(lean_object* v_Deleted_484_){
_start:
{
lean_inc(v_Deleted_484_);
return v_Deleted_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Deleted_elim___redArg___boxed(lean_object* v_Deleted_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_Lsp_FileChangeType_Deleted_elim___redArg(v_Deleted_485_);
lean_dec(v_Deleted_485_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Deleted_elim(lean_object* v_motive_487_, uint8_t v_t_488_, lean_object* v_h_489_, lean_object* v_Deleted_490_){
_start:
{
lean_inc(v_Deleted_490_);
return v_Deleted_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Deleted_elim___boxed(lean_object* v_motive_491_, lean_object* v_t_492_, lean_object* v_h_493_, lean_object* v_Deleted_494_){
_start:
{
uint8_t v_t_boxed_495_; lean_object* v_res_496_; 
v_t_boxed_495_ = lean_unbox(v_t_492_);
v_res_496_ = l_Lean_Lsp_FileChangeType_Deleted_elim(v_motive_491_, v_t_boxed_495_, v_h_493_, v_Deleted_494_);
lean_dec(v_Deleted_494_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonFileChangeType___lam__0(lean_object* v_j_507_){
_start:
{
lean_object* v___x_508_; 
lean_inc(v_j_507_);
v___x_508_ = l_Lean_Json_getNat_x3f(v_j_507_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec(v_j_507_);
v_a_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_537_; 
v_a_517_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_537_ == 0)
{
v___x_519_ = v___x_508_;
v_isShared_520_ = v_isSharedCheck_537_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_508_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_537_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = lean_unsigned_to_nat(1u);
v___x_522_ = lean_nat_dec_eq(v_a_517_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = lean_unsigned_to_nat(2u);
v___x_524_ = lean_nat_dec_eq(v_a_517_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = lean_unsigned_to_nat(3u);
v___x_526_ = lean_nat_dec_eq(v_a_517_, v___x_525_);
lean_dec(v_a_517_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_527_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__0));
v___x_528_ = lean_unsigned_to_nat(80u);
v___x_529_ = l_Lean_Json_pretty(v_j_507_, v___x_528_);
v___x_530_ = lean_string_append(v___x_527_, v___x_529_);
lean_dec_ref(v___x_529_);
if (v_isShared_520_ == 0)
{
lean_ctor_set_tag(v___x_519_, 0);
lean_ctor_set(v___x_519_, 0, v___x_530_);
v___x_532_ = v___x_519_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
else
{
lean_object* v___x_534_; 
lean_del_object(v___x_519_);
lean_dec(v_j_507_);
v___x_534_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__1));
return v___x_534_;
}
}
else
{
lean_object* v___x_535_; 
lean_del_object(v___x_519_);
lean_dec(v_a_517_);
lean_dec(v_j_507_);
v___x_535_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__2));
return v___x_535_;
}
}
else
{
lean_object* v___x_536_; 
lean_del_object(v___x_519_);
lean_dec(v_a_517_);
lean_dec(v_j_507_);
v___x_536_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__3));
return v___x_536_;
}
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = l_Lean_JsonNumber_fromNat(v___x_540_);
return v___x_541_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0);
v___x_543_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_unsigned_to_nat(2u);
v___x_545_ = l_Lean_JsonNumber_fromNat(v___x_544_);
return v___x_545_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2);
v___x_547_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_unsigned_to_nat(3u);
v___x_549_ = l_Lean_JsonNumber_fromNat(v___x_548_);
return v___x_549_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4);
v___x_551_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileChangeType___lam__0(uint8_t v_x_552_){
_start:
{
switch(v_x_552_)
{
case 0:
{
lean_object* v___x_553_; 
v___x_553_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1);
return v___x_553_;
}
case 1:
{
lean_object* v___x_554_; 
v___x_554_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3);
return v___x_554_;
}
default: 
{
lean_object* v___x_555_; 
v___x_555_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5);
return v___x_555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileChangeType___lam__0___boxed(lean_object* v_x_556_){
_start:
{
uint8_t v_x_102__boxed_557_; lean_object* v_res_558_; 
v_x_102__boxed_557_ = lean_unbox(v_x_556_);
v_res_558_ = l_Lean_Lsp_instToJsonFileChangeType___lam__0(v_x_102__boxed_557_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0(lean_object* v_j_561_, lean_object* v_k_562_){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = l_Lean_Json_getObjValD(v_j_561_, v_k_562_);
lean_inc(v___x_563_);
v___x_564_ = l_Lean_Json_getNat_x3f(v___x_563_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_dec(v___x_563_);
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_593_; 
v_a_573_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_593_ == 0)
{
v___x_575_ = v___x_564_;
v_isShared_576_ = v_isSharedCheck_593_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_564_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_593_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_577_ = lean_unsigned_to_nat(1u);
v___x_578_ = lean_nat_dec_eq(v_a_573_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = lean_unsigned_to_nat(2u);
v___x_580_ = lean_nat_dec_eq(v_a_573_, v___x_579_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_581_ = lean_unsigned_to_nat(3u);
v___x_582_ = lean_nat_dec_eq(v_a_573_, v___x_581_);
lean_dec(v_a_573_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_583_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__0));
v___x_584_ = lean_unsigned_to_nat(80u);
v___x_585_ = l_Lean_Json_pretty(v___x_563_, v___x_584_);
v___x_586_ = lean_string_append(v___x_583_, v___x_585_);
lean_dec_ref(v___x_585_);
if (v_isShared_576_ == 0)
{
lean_ctor_set_tag(v___x_575_, 0);
lean_ctor_set(v___x_575_, 0, v___x_586_);
v___x_588_ = v___x_575_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
else
{
lean_object* v___x_590_; 
lean_del_object(v___x_575_);
lean_dec(v___x_563_);
v___x_590_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__1));
return v___x_590_;
}
}
else
{
lean_object* v___x_591_; 
lean_del_object(v___x_575_);
lean_dec(v_a_573_);
lean_dec(v___x_563_);
v___x_591_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__2));
return v___x_591_;
}
}
else
{
lean_object* v___x_592_; 
lean_del_object(v___x_575_);
lean_dec(v_a_573_);
lean_dec(v___x_563_);
v___x_592_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__3));
return v___x_592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0___boxed(lean_object* v_j_594_, lean_object* v_k_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0(v_j_594_, v_k_595_);
lean_dec_ref(v_k_595_);
return v_res_596_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2(void){
_start:
{
uint8_t v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_602_ = 1;
v___x_603_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1));
v___x_604_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_603_, v___x_602_);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5));
v___x_606_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2);
v___x_607_ = lean_string_append(v___x_606_, v___x_605_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_608_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8);
v___x_609_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3);
v___x_610_ = lean_string_append(v___x_609_, v___x_608_);
return v___x_610_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
v___x_612_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4);
v___x_613_ = lean_string_append(v___x_612_, v___x_611_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8(void){
_start:
{
uint8_t v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_617_ = 1;
v___x_618_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__7));
v___x_619_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_618_, v___x_617_);
return v___x_619_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_620_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8);
v___x_621_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3);
v___x_622_ = lean_string_append(v___x_621_, v___x_620_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
v___x_624_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9);
v___x_625_ = lean_string_append(v___x_624_, v___x_623_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonFileEvent_fromJson(lean_object* v_json_626_){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0));
lean_inc(v_json_626_);
v___x_628_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(v_json_626_, v___x_627_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_638_; 
lean_dec(v_json_626_);
v_a_629_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_638_ == 0)
{
v___x_631_ = v___x_628_;
v_isShared_632_ = v_isSharedCheck_638_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_628_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_638_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_633_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5);
v___x_634_ = lean_string_append(v___x_633_, v_a_629_);
lean_dec(v_a_629_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_634_);
v___x_636_ = v___x_631_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec(v_json_626_);
v_a_639_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_628_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_628_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set_tag(v___x_641_, 0);
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v_a_647_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_a_647_);
lean_dec_ref(v___x_628_);
v___x_648_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6));
v___x_649_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0(v_json_626_, v___x_648_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_659_; 
lean_dec(v_a_647_);
v_a_650_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_659_ == 0)
{
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_659_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_659_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_654_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10);
v___x_655_ = lean_string_append(v___x_654_, v_a_650_);
lean_dec(v_a_650_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_655_);
v___x_657_ = v___x_652_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
else
{
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec(v_a_647_);
v_a_660_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_649_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_649_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set_tag(v___x_662_, 0);
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
else
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_677_; 
v_a_668_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_677_ == 0)
{
v___x_670_ = v___x_649_;
v_isShared_671_ = v_isSharedCheck_677_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_649_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_677_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; uint8_t v___x_673_; lean_object* v___x_675_; 
v___x_672_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_672_, 0, v_a_647_);
v___x_673_ = lean_unbox(v_a_668_);
lean_dec(v_a_668_);
lean_ctor_set_uint8(v___x_672_, sizeof(void*)*1, v___x_673_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_672_);
v___x_675_ = v___x_670_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_672_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileEvent_toJson(lean_object* v_x_680_){
_start:
{
lean_object* v_uri_681_; uint8_t v_type_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___y_690_; 
v_uri_681_ = lean_ctor_get(v_x_680_, 0);
v_type_682_ = lean_ctor_get_uint8(v_x_680_, sizeof(void*)*1);
v___x_683_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0));
lean_inc_ref(v_uri_681_);
v___x_684_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_684_, 0, v_uri_681_);
v___x_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_683_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = lean_box(0);
v___x_687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_685_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6));
switch(v_type_682_)
{
case 0:
{
lean_object* v___x_698_; 
v___x_698_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1);
v___y_690_ = v___x_698_;
goto v___jp_689_;
}
case 1:
{
lean_object* v___x_699_; 
v___x_699_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3);
v___y_690_ = v___x_699_;
goto v___jp_689_;
}
default: 
{
lean_object* v___x_700_; 
v___x_700_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5);
v___y_690_ = v___x_700_;
goto v___jp_689_;
}
}
v___jp_689_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
lean_inc(v___y_690_);
v___x_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_688_);
lean_ctor_set(v___x_691_, 1, v___y_690_);
v___x_692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v___x_686_);
v___x_693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
lean_ctor_set(v___x_693_, 1, v___x_686_);
v___x_694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_687_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2));
v___x_696_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(v___x_694_, v___x_695_);
v___x_697_ = l_Lean_Json_mkObj(v___x_696_);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileEvent_toJson___boxed(lean_object* v_x_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_Lsp_instToJsonFileEvent_toJson(v_x_701_);
lean_dec_ref(v_x_701_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1(size_t v_sz_705_, size_t v_i_706_, lean_object* v_bs_707_){
_start:
{
uint8_t v___x_708_; 
v___x_708_ = lean_usize_dec_lt(v_i_706_, v_sz_705_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; 
v___x_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_709_, 0, v_bs_707_);
return v___x_709_;
}
else
{
lean_object* v_v_710_; lean_object* v___x_711_; 
v_v_710_ = lean_array_uget_borrowed(v_bs_707_, v_i_706_);
lean_inc(v_v_710_);
v___x_711_ = l_Lean_Lsp_instFromJsonFileEvent_fromJson(v_v_710_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec_ref(v_bs_707_);
v_a_712_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_711_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
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
lean_object* v_a_720_; lean_object* v___x_721_; lean_object* v_bs_x27_722_; size_t v___x_723_; size_t v___x_724_; lean_object* v___x_725_; 
v_a_720_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_720_);
lean_dec_ref(v___x_711_);
v___x_721_ = lean_unsigned_to_nat(0u);
v_bs_x27_722_ = lean_array_uset(v_bs_707_, v_i_706_, v___x_721_);
v___x_723_ = ((size_t)1ULL);
v___x_724_ = lean_usize_add(v_i_706_, v___x_723_);
v___x_725_ = lean_array_uset(v_bs_x27_722_, v_i_706_, v_a_720_);
v_i_706_ = v___x_724_;
v_bs_707_ = v___x_725_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_727_, lean_object* v_i_728_, lean_object* v_bs_729_){
_start:
{
size_t v_sz_boxed_730_; size_t v_i_boxed_731_; lean_object* v_res_732_; 
v_sz_boxed_730_ = lean_unbox_usize(v_sz_727_);
lean_dec(v_sz_727_);
v_i_boxed_731_ = lean_unbox_usize(v_i_728_);
lean_dec(v_i_728_);
v_res_732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_730_, v_i_boxed_731_, v_bs_729_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0(lean_object* v_x_733_){
_start:
{
if (lean_obj_tag(v_x_733_) == 4)
{
lean_object* v_elems_734_; size_t v_sz_735_; size_t v___x_736_; lean_object* v___x_737_; 
v_elems_734_ = lean_ctor_get(v_x_733_, 0);
lean_inc_ref(v_elems_734_);
lean_dec_ref(v_x_733_);
v_sz_735_ = lean_array_size(v_elems_734_);
v___x_736_ = ((size_t)0ULL);
v___x_737_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1(v_sz_735_, v___x_736_, v_elems_734_);
return v___x_737_;
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_738_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0));
v___x_739_ = lean_unsigned_to_nat(80u);
v___x_740_ = l_Lean_Json_pretty(v_x_733_, v___x_739_);
v___x_741_ = lean_string_append(v___x_738_, v___x_740_);
lean_dec_ref(v___x_740_);
v___x_742_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1));
v___x_743_ = lean_string_append(v___x_741_, v___x_742_);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0(lean_object* v_j_745_, lean_object* v_k_746_){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = l_Lean_Json_getObjValD(v_j_745_, v_k_746_);
v___x_748_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0(v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0___boxed(lean_object* v_j_749_, lean_object* v_k_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0(v_j_749_, v_k_750_);
lean_dec_ref(v_k_750_);
return v_res_751_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_758_ = 1;
v___x_759_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2));
v___x_760_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_759_, v___x_758_);
return v___x_760_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_761_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5));
v___x_762_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3);
v___x_763_ = lean_string_append(v___x_762_, v___x_761_);
return v___x_763_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = 1;
v___x_767_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__5));
v___x_768_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_767_, v___x_766_);
return v___x_768_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_769_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6);
v___x_770_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4);
v___x_771_ = lean_string_append(v___x_770_, v___x_769_);
return v___x_771_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_772_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
v___x_773_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7);
v___x_774_ = lean_string_append(v___x_773_, v___x_772_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson(lean_object* v_json_775_){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0));
v___x_777_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0(v_json_775_, v___x_776_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_787_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_787_ == 0)
{
v___x_780_ = v___x_777_;
v_isShared_781_ = v_isSharedCheck_787_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_787_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_782_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8);
v___x_783_ = lean_string_append(v___x_782_, v_a_778_);
lean_dec(v_a_778_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_783_);
v___x_785_ = v___x_780_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
else
{
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
v_a_788_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_777_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_777_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set_tag(v___x_790_, 0);
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
v_a_796_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_777_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_777_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0(size_t v_sz_806_, size_t v_i_807_, lean_object* v_bs_808_){
_start:
{
uint8_t v___x_809_; 
v___x_809_ = lean_usize_dec_lt(v_i_807_, v_sz_806_);
if (v___x_809_ == 0)
{
return v_bs_808_;
}
else
{
lean_object* v_v_810_; lean_object* v___x_811_; lean_object* v_bs_x27_812_; lean_object* v___x_813_; size_t v___x_814_; size_t v___x_815_; lean_object* v___x_816_; 
v_v_810_ = lean_array_uget(v_bs_808_, v_i_807_);
v___x_811_ = lean_unsigned_to_nat(0u);
v_bs_x27_812_ = lean_array_uset(v_bs_808_, v_i_807_, v___x_811_);
v___x_813_ = l_Lean_Lsp_instToJsonFileEvent_toJson(v_v_810_);
lean_dec(v_v_810_);
v___x_814_ = ((size_t)1ULL);
v___x_815_ = lean_usize_add(v_i_807_, v___x_814_);
v___x_816_ = lean_array_uset(v_bs_x27_812_, v_i_807_, v___x_813_);
v_i_807_ = v___x_815_;
v_bs_808_ = v___x_816_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_818_, lean_object* v_i_819_, lean_object* v_bs_820_){
_start:
{
size_t v_sz_boxed_821_; size_t v_i_boxed_822_; lean_object* v_res_823_; 
v_sz_boxed_821_ = lean_unbox_usize(v_sz_818_);
lean_dec(v_sz_818_);
v_i_boxed_822_ = lean_unbox_usize(v_i_819_);
lean_dec(v_i_819_);
v_res_823_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0(v_sz_boxed_821_, v_i_boxed_822_, v_bs_820_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0(lean_object* v_a_824_){
_start:
{
size_t v_sz_825_; size_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v_sz_825_ = lean_array_size(v_a_824_);
v___x_826_ = ((size_t)0ULL);
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0(v_sz_825_, v___x_826_, v_a_824_);
v___x_828_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson(lean_object* v_x_829_){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_830_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0));
v___x_831_ = l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0(v_x_829_);
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = lean_box(0);
v___x_834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v___x_833_);
v___x_836_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2));
v___x_837_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(v___x_835_, v___x_836_);
v___x_838_ = l_Lean_Json_mkObj(v___x_837_);
return v___x_838_;
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Workspace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Lsp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_FileSystemWatcher_create = _init_l_Lean_Lsp_FileSystemWatcher_create();
lean_mark_persistent(l_Lean_Lsp_FileSystemWatcher_create);
l_Lean_Lsp_FileSystemWatcher_change = _init_l_Lean_Lsp_FileSystemWatcher_change();
lean_mark_persistent(l_Lean_Lsp_FileSystemWatcher_change);
l_Lean_Lsp_FileSystemWatcher_delete = _init_l_Lean_Lsp_FileSystemWatcher_delete();
lean_mark_persistent(l_Lean_Lsp_FileSystemWatcher_delete);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Lsp_Workspace(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Lsp_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Workspace(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Lsp_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Lsp_Workspace(builtin);
}
#ifdef __cplusplus
}
#endif
