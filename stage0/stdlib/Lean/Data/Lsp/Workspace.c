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
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "uri"};
static const lean_object* l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2_value;
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkspaceFolder_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonWorkspaceFolder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonWorkspaceFolder_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonWorkspaceFolder___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceFolder___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonWorkspaceFolder = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceFolder___closed__0_value;
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Lsp"};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "WorkspaceFolder"};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__2_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 202, 85, 200, 38, 26, 140, 92)}};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value;
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4;
static const lean_string_object l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5_value;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6;
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
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
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonFileSystemWatcher_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileSystemWatcher_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonFileSystemWatcher___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonFileSystemWatcher_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonFileSystemWatcher___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonFileSystemWatcher___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonFileSystemWatcher = (const lean_object*)&l_Lean_Lsp_instToJsonFileSystemWatcher___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_FileSystemWatcher_create;
LEAN_EXPORT lean_object* l_Lean_Lsp_FileSystemWatcher_change;
LEAN_EXPORT lean_object* l_Lean_Lsp_FileSystemWatcher_delete;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1_value;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
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
lean_object* lean_array_uget(lean_object*, size_t);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_List_foldl___at___00Array_appendList_spec__0___redArg(x_2, x_4);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkspaceFolder_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_23; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
x_4 = x_1;
x_5 = x_23;
goto block_22;
}
else
{
lean_inc(x_3);
lean_inc(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0));
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_2);
if (x_5 == 0)
{
lean_ctor_set(x_4, 1, x_7);
lean_ctor_set(x_4, 0, x_6);
x_8 = x_4;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_7);
x_8 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1));
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2));
x_18 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(x_16, x_17);
x_19 = l_Lean_Json_mkObj(x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getStr_x3f(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__7));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__9, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__9);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__13(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__12));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__13, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__13);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__14, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__14);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0));
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_13; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
x_5 = x_3;
x_6 = x_13;
goto block_12;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__11, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__11);
x_8 = lean_string_append(x_7, x_4);
lean_dec(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_8);
x_9 = x_5;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_3, 0);
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
x_15 = x_3;
x_16 = x_21;
goto block_20;
}
else
{
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 0);
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec_ref(x_3);
x_23 = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1));
x_24 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(x_1, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_34; 
lean_dec(x_22);
x_25 = lean_ctor_get(x_24, 0);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
x_26 = x_24;
x_27 = x_34;
goto block_33;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15);
x_29 = lean_string_append(x_28, x_25);
lean_dec(x_25);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_29);
x_30 = x_26;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
else
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec(x_22);
x_35 = lean_ctor_get(x_24, 0);
x_42 = !lean_is_exclusive(x_24);
if (x_42 == 0)
{
x_36 = x_24;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_24);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
lean_ctor_set_tag(x_36, 0);
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_51; 
x_43 = lean_ctor_get(x_24, 0);
x_51 = !lean_is_exclusive(x_24);
if (x_51 == 0)
{
x_44 = x_24;
x_45 = x_51;
goto block_50;
}
else
{
lean_inc(x_43);
lean_dec(x_24);
x_44 = lean_box(0);
x_45 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_22);
lean_ctor_set(x_46, 1, x_43);
if (x_45 == 0)
{
lean_ctor_set(x_44, 0, x_46);
x_47 = x_44;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_46);
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
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Json_getNat_x3f(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_12 = lean_ctor_get(x_3, 0);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
x_13 = x_3;
x_14 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
if (x_14 == 0)
{
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__5));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__11));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__0));
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_13; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
x_5 = x_3;
x_6 = x_13;
goto block_12;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8);
x_8 = lean_string_append(x_7, x_4);
lean_dec(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_8);
x_9 = x_5;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_3, 0);
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
x_15 = x_3;
x_16 = x_21;
goto block_20;
}
else
{
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 0);
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec_ref(x_3);
x_23 = ((lean_object*)(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__9));
x_24 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0(x_1, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_34; 
lean_dec(x_22);
x_25 = lean_ctor_get(x_24, 0);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
x_26 = x_24;
x_27 = x_34;
goto block_33;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14);
x_29 = lean_string_append(x_28, x_25);
lean_dec(x_25);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_29);
x_30 = x_26;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
else
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec(x_22);
x_35 = lean_ctor_get(x_24, 0);
x_42 = !lean_is_exclusive(x_24);
if (x_42 == 0)
{
x_36 = x_24;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_24);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
lean_ctor_set_tag(x_36, 0);
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_51; 
x_43 = lean_ctor_get(x_24, 0);
x_51 = !lean_is_exclusive(x_24);
if (x_51 == 0)
{
x_44 = x_24;
x_45 = x_51;
goto block_50;
}
else
{
lean_inc(x_43);
lean_dec(x_24);
x_44 = lean_box(0);
x_45 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_22);
lean_ctor_set(x_46, 1, x_43);
if (x_45 == 0)
{
lean_ctor_set(x_44, 0, x_46);
x_47 = x_44;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_46);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonFileSystemWatcher_toJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_15; 
x_4 = lean_ctor_get(x_2, 0);
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
x_5 = x_2;
x_6 = x_15;
goto block_14;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_JsonNumber_fromNat(x_4);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 2);
lean_ctor_set(x_5, 0, x_7);
x_8 = x_5;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_7);
x_8 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileSystemWatcher_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_21; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
x_4 = x_1;
x_5 = x_21;
goto block_20;
}
else
{
lean_inc(x_3);
lean_inc(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = ((lean_object*)(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__0));
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_2);
if (x_5 == 0)
{
lean_ctor_set(x_4, 1, x_7);
lean_ctor_set(x_4, 0, x_6);
x_8 = x_4;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_7);
x_8 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = ((lean_object*)(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__9));
x_12 = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonFileSystemWatcher_toJson_spec__0(x_11, x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2));
x_16 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(x_14, x_15);
x_17 = l_Lean_Json_mkObj(x_16);
return x_17;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_FileSystemWatcher_create(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_FileSystemWatcher_change(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2u);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_FileSystemWatcher_delete(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(4u);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget_borrowed(x_3, x_2);
lean_inc(x_6);
x_7 = l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_15; 
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_7, 0);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
x_9 = x_7;
x_10 = x_15;
goto block_14;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_11; 
if (x_10 == 0)
{
x_11 = x_9;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_8);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
lean_dec_ref(x_7);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_3, x_2, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_18, x_2, x_16);
x_2 = x_20;
x_3 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0));
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__5));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0));
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_13; 
x_4 = lean_ctor_get(x_3, 0);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
x_5 = x_3;
x_6 = x_13;
goto block_12;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8);
x_8 = lean_string_append(x_7, x_4);
lean_dec(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_8);
x_9 = x_5;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
x_14 = lean_ctor_get(x_3, 0);
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
x_15 = x_3;
x_16 = x_21;
goto block_20;
}
else
{
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 0);
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
x_22 = lean_ctor_get(x_3, 0);
x_29 = !lean_is_exclusive(x_3);
if (x_29 == 0)
{
x_23 = x_3;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Lsp_instToJsonFileSystemWatcher_toJson(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0));
x_3 = l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2));
x_9 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(x_7, x_8);
x_10 = l_Lean_Json_mkObj(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Lsp_FileChangeType_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_FileChangeType_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Lsp_FileChangeType_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_FileChangeType_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_Lsp_FileChangeType_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Created_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Created_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_FileChangeType_Created_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Created_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Created_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Lsp_FileChangeType_Created_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Changed_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Changed_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_FileChangeType_Changed_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Changed_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Changed_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Lsp_FileChangeType_Changed_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Deleted_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Deleted_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_FileChangeType_Deleted_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Deleted_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Deleted_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Lsp_FileChangeType_Deleted_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonFileChangeType___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Json_getNat_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
x_4 = x_2;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_31; 
x_11 = lean_ctor_get(x_2, 0);
x_31 = !lean_is_exclusive(x_2);
if (x_31 == 0)
{
x_12 = x_2;
x_13 = x_31;
goto block_30;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_dec_eq(x_11, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_dec_eq(x_11, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(3u);
x_19 = lean_nat_dec_eq(x_11, x_18);
lean_dec(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__0));
x_21 = lean_unsigned_to_nat(80u);
x_22 = l_Lean_Json_pretty(x_1, x_21);
x_23 = lean_string_append(x_20, x_22);
lean_dec_ref(x_22);
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_23);
x_24 = x_12;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
else
{
lean_object* x_27; 
lean_del_object(x_12);
lean_dec(x_1);
x_27 = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__1));
return x_27;
}
}
else
{
lean_object* x_28; 
lean_del_object(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_28 = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__2));
return x_28;
}
}
else
{
lean_object* x_29; 
lean_del_object(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_29 = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__3));
return x_29;
}
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_JsonNumber_fromNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_Lean_JsonNumber_fromNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_JsonNumber_fromNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileChangeType___lam__0(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileChangeType___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Lsp_instToJsonFileChangeType___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
lean_inc(x_3);
x_4 = l_Lean_Json_getNat_x3f(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_12; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
x_6 = x_4;
x_7 = x_12;
goto block_11;
}
else
{
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_8; 
if (x_7 == 0)
{
x_8 = x_6;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_5);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_33; 
x_13 = lean_ctor_get(x_4, 0);
x_33 = !lean_is_exclusive(x_4);
if (x_33 == 0)
{
x_14 = x_4;
x_15 = x_33;
goto block_32;
}
else
{
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_dec_eq(x_13, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_nat_dec_eq(x_13, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(3u);
x_21 = lean_nat_dec_eq(x_13, x_20);
lean_dec(x_13);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__0));
x_23 = lean_unsigned_to_nat(80u);
x_24 = l_Lean_Json_pretty(x_3, x_23);
x_25 = lean_string_append(x_22, x_24);
lean_dec_ref(x_24);
if (x_15 == 0)
{
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_25);
x_26 = x_14;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
else
{
lean_object* x_29; 
lean_del_object(x_14);
lean_dec(x_3);
x_29 = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__1));
return x_29;
}
}
else
{
lean_object* x_30; 
lean_del_object(x_14);
lean_dec(x_13);
lean_dec(x_3);
x_30 = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__2));
return x_30;
}
}
else
{
lean_object* x_31; 
lean_del_object(x_14);
lean_dec(x_13);
lean_dec(x_3);
x_31 = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__3));
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__7));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonFileEvent_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0));
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_13; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
x_5 = x_3;
x_6 = x_13;
goto block_12;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5);
x_8 = lean_string_append(x_7, x_4);
lean_dec(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_8);
x_9 = x_5;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_3, 0);
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
x_15 = x_3;
x_16 = x_21;
goto block_20;
}
else
{
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 0);
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec_ref(x_3);
x_23 = ((lean_object*)(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6));
x_24 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0(x_1, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_34; 
lean_dec(x_22);
x_25 = lean_ctor_get(x_24, 0);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
x_26 = x_24;
x_27 = x_34;
goto block_33;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10);
x_29 = lean_string_append(x_28, x_25);
lean_dec(x_25);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_29);
x_30 = x_26;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
else
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec(x_22);
x_35 = lean_ctor_get(x_24, 0);
x_42 = !lean_is_exclusive(x_24);
if (x_42 == 0)
{
x_36 = x_24;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_24);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
lean_ctor_set_tag(x_36, 0);
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_52; 
x_43 = lean_ctor_get(x_24, 0);
x_52 = !lean_is_exclusive(x_24);
if (x_52 == 0)
{
x_44 = x_24;
x_45 = x_52;
goto block_51;
}
else
{
lean_inc(x_43);
lean_dec(x_24);
x_44 = lean_box(0);
x_45 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_22);
x_47 = lean_unbox(x_43);
lean_dec(x_43);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_47);
if (x_45 == 0)
{
lean_ctor_set(x_44, 0, x_46);
x_48 = x_44;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_46);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileEvent_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_4 = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0));
lean_inc_ref(x_2);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = ((lean_object*)(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6));
switch (x_3) {
case 0:
{
lean_object* x_19; 
x_19 = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1);
x_10 = x_19;
goto block_18;
}
case 1:
{
lean_object* x_20; 
x_20 = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3);
x_10 = x_20;
goto block_18;
}
default: 
{
lean_object* x_21; 
x_21 = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5);
x_10 = x_21;
goto block_18;
}
}
block_18:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
x_15 = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2));
x_16 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(x_14, x_15);
x_17 = l_Lean_Json_mkObj(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileEvent_toJson___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instToJsonFileEvent_toJson(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget_borrowed(x_3, x_2);
lean_inc(x_6);
x_7 = l_Lean_Lsp_instFromJsonFileEvent_fromJson(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_15; 
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_7, 0);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
x_9 = x_7;
x_10 = x_15;
goto block_14;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_11; 
if (x_10 == 0)
{
x_11 = x_9;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_8);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
lean_dec_ref(x_7);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_3, x_2, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_18, x_2, x_16);
x_2 = x_20;
x_3 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0));
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__5));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0));
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_13; 
x_4 = lean_ctor_get(x_3, 0);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
x_5 = x_3;
x_6 = x_13;
goto block_12;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8);
x_8 = lean_string_append(x_7, x_4);
lean_dec(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_8);
x_9 = x_5;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
x_14 = lean_ctor_get(x_3, 0);
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
x_15 = x_3;
x_16 = x_21;
goto block_20;
}
else
{
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 0);
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
x_22 = lean_ctor_get(x_3, 0);
x_29 = !lean_is_exclusive(x_3);
if (x_29 == 0)
{
x_23 = x_3;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Lsp_instToJsonFileEvent_toJson(x_5);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0));
x_3 = l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2));
x_9 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(x_7, x_8);
x_10 = l_Lean_Json_mkObj(x_9);
return x_10;
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Workspace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Lsp_Basic(builtin)
;
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
res = initialize_Lean_Data_Lsp_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Workspace(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Lsp_Workspace(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Lsp_Workspace(builtin);
}
#ifdef __cplusplus
}
#endif
