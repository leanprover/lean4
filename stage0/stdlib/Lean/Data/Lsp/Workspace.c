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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_obj_tag_nat(lean_object*);
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
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions = (const lean_object*)&l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0(lean_object*);
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
lean_dec_ref_known(v_a_1_, 2);
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
lean_dec(v___x_31_);
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
lean_dec_ref_known(v___x_83_, 1);
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
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0(lean_object* v_x_136_){
_start:
{
if (lean_obj_tag(v_x_136_) == 0)
{
lean_object* v___x_137_; 
v___x_137_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0___closed__0));
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
v___x_159_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0(v___x_158_);
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
lean_dec_ref_known(v___x_201_, 1);
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
lean_dec(v___x_284_);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1(size_t v_sz_293_, size_t v_i_294_, lean_object* v_bs_295_){
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
lean_dec_ref_known(v___x_299_, 1);
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_293_ = stack[0].m_num;
size_t v_i_294_ = stack[1].m_num;
lean_object* v_bs_295_ = stack[2].m_obj;
lean_object* v_res_315_;
v_res_315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1(v_sz_293_, v_i_294_, v_bs_295_);
stack->m_obj
 = v_res_315_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_316_, lean_object* v_i_317_, lean_object* v_bs_318_){
_start:
{
size_t v_sz_boxed_319_; size_t v_i_boxed_320_; lean_object* v_res_321_; 
v_sz_boxed_319_ = lean_unbox_usize(v_sz_316_);
lean_dec(v_sz_316_);
v_i_boxed_320_ = lean_unbox_usize(v_i_317_);
lean_dec(v_i_317_);
v_res_321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_319_, v_i_boxed_320_, v_bs_318_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0(lean_object* v_x_324_){
_start:
{
if (lean_obj_tag(v_x_324_) == 4)
{
lean_object* v_elems_325_; size_t v_sz_326_; size_t v___x_327_; lean_object* v___x_328_; 
v_elems_325_ = lean_ctor_get(v_x_324_, 0);
lean_inc_ref(v_elems_325_);
lean_dec_ref_known(v_x_324_, 1);
v_sz_326_ = lean_array_size(v_elems_325_);
v___x_327_ = ((size_t)0ULL);
v___x_328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1(v_sz_326_, v___x_327_, v_elems_325_);
return v___x_328_;
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_329_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0));
v___x_330_ = lean_unsigned_to_nat(80u);
v___x_331_ = l_Lean_Json_pretty(v_x_324_, v___x_330_);
v___x_332_ = lean_string_append(v___x_329_, v___x_331_);
lean_dec_ref(v___x_331_);
v___x_333_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1));
v___x_334_ = lean_string_append(v___x_332_, v___x_333_);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0(lean_object* v_j_336_, lean_object* v_k_337_){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = l_Lean_Json_getObjValD(v_j_336_, v_k_337_);
v___x_339_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0(v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0___boxed(lean_object* v_j_340_, lean_object* v_k_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0(v_j_340_, v_k_341_);
lean_dec_ref(v_k_341_);
return v_res_342_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3(void){
_start:
{
uint8_t v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_349_ = 1;
v___x_350_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2));
v___x_351_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_350_, v___x_349_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5));
v___x_353_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3);
v___x_354_ = lean_string_append(v___x_353_, v___x_352_);
return v___x_354_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6(void){
_start:
{
uint8_t v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = 1;
v___x_358_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__5));
v___x_359_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_358_, v___x_357_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_360_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6);
v___x_361_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4);
v___x_362_ = lean_string_append(v___x_361_, v___x_360_);
return v___x_362_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_363_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
v___x_364_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7);
v___x_365_ = lean_string_append(v___x_364_, v___x_363_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson(lean_object* v_json_366_){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0));
v___x_368_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0(v_json_366_, v___x_367_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_378_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_378_ == 0)
{
v___x_371_ = v___x_368_;
v_isShared_372_ = v_isSharedCheck_378_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_378_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_373_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8);
v___x_374_ = lean_string_append(v___x_373_, v_a_369_);
lean_dec(v_a_369_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_374_);
v___x_376_ = v___x_371_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
else
{
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
v_a_379_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_368_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_368_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
lean_ctor_set_tag(v___x_381_, 0);
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
v_a_387_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_368_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_368_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0(size_t v_sz_397_, size_t v_i_398_, lean_object* v_bs_399_){
_start:
{
uint8_t v___x_400_; 
v___x_400_ = lean_usize_dec_lt(v_i_398_, v_sz_397_);
if (v___x_400_ == 0)
{
return v_bs_399_;
}
else
{
lean_object* v_v_401_; lean_object* v___x_402_; lean_object* v_bs_x27_403_; lean_object* v___x_404_; size_t v___x_405_; size_t v___x_406_; lean_object* v___x_407_; 
v_v_401_ = lean_array_uget(v_bs_399_, v_i_398_);
v___x_402_ = lean_unsigned_to_nat(0u);
v_bs_x27_403_ = lean_array_uset(v_bs_399_, v_i_398_, v___x_402_);
v___x_404_ = l_Lean_Lsp_instToJsonFileSystemWatcher_toJson(v_v_401_);
v___x_405_ = ((size_t)1ULL);
v___x_406_ = lean_usize_add(v_i_398_, v___x_405_);
v___x_407_ = lean_array_uset(v_bs_x27_403_, v_i_398_, v___x_404_);
v_i_398_ = v___x_406_;
v_bs_399_ = v___x_407_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_397_ = stack[0].m_num;
size_t v_i_398_ = stack[1].m_num;
lean_object* v_bs_399_ = stack[2].m_obj;
lean_object* v_res_409_;
v_res_409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0(v_sz_397_, v_i_398_, v_bs_399_);
stack->m_obj
 = v_res_409_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0___boxed(lean_object* v_sz_410_, lean_object* v_i_411_, lean_object* v_bs_412_){
_start:
{
size_t v_sz_boxed_413_; size_t v_i_boxed_414_; lean_object* v_res_415_; 
v_sz_boxed_413_ = lean_unbox_usize(v_sz_410_);
lean_dec(v_sz_410_);
v_i_boxed_414_ = lean_unbox_usize(v_i_411_);
lean_dec(v_i_411_);
v_res_415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0(v_sz_boxed_413_, v_i_boxed_414_, v_bs_412_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0(lean_object* v_a_416_){
_start:
{
size_t v_sz_417_; size_t v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v_sz_417_ = lean_array_size(v_a_416_);
v___x_418_ = ((size_t)0ULL);
v___x_419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0(v_sz_417_, v___x_418_, v_a_416_);
v___x_420_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson(lean_object* v_x_421_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_422_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0));
v___x_423_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0(v_x_421_);
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_422_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = lean_box(0);
v___x_426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_424_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v___x_427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set(v___x_427_, 1, v___x_425_);
v___x_428_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2));
v___x_429_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(v___x_427_, v___x_428_);
v___x_430_ = l_Lean_Json_mkObj(v___x_429_);
lean_dec(v___x_429_);
return v___x_430_;
}
}
lean_object* l_Lean_Lsp_FileChangeType_ctorIdx___impl(uint8_t v_x_433_){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_box(v_x_433_);
v___x_435_ = lean_obj_tag_nat(v___x_434_);
lean_dec(v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT void l_Lean_Lsp_FileChangeType_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_433_ = stack[0].m_num;
lean_object* v_res_436_;
v_res_436_ = l_Lean_Lsp_FileChangeType_ctorIdx___impl(v_x_433_);
stack->m_obj
 = v_res_436_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorIdx___impl___boxed(lean_object* v_x_437_){
_start:
{
uint8_t v_x_4__boxed_438_; lean_object* v_res_439_; 
v_x_4__boxed_438_ = lean_unbox(v_x_437_);
v_res_439_ = l_Lean_Lsp_FileChangeType_ctorIdx___impl(v_x_4__boxed_438_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorElim___redArg(lean_object* v_k_440_){
_start:
{
lean_inc(v_k_440_);
return v_k_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorElim___redArg___boxed(lean_object* v_k_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_Lsp_FileChangeType_ctorElim___redArg(v_k_441_);
lean_dec(v_k_441_);
return v_res_442_;
}
}
lean_object* l_Lean_Lsp_FileChangeType_ctorElim(lean_object* v_motive_443_, lean_object* v_ctorIdx_444_, uint8_t v_t_445_, lean_object* v_h_446_, lean_object* v_k_447_){
_start:
{
lean_inc(v_k_447_);
return v_k_447_;
}
}
LEAN_EXPORT void l_Lean_Lsp_FileChangeType_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_444_ = stack[1].m_obj;
uint8_t v_t_445_ = stack[2].m_num;
lean_object* v_k_447_ = stack[4].m_obj;
lean_object* v_res_448_;
v_res_448_ = l_Lean_Lsp_FileChangeType_ctorElim(lean_box(0), v_ctorIdx_444_, v_t_445_, lean_box(0), v_k_447_);
stack->m_obj
 = v_res_448_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorElim___boxed(lean_object* v_motive_449_, lean_object* v_ctorIdx_450_, lean_object* v_t_451_, lean_object* v_h_452_, lean_object* v_k_453_){
_start:
{
uint8_t v_t_boxed_454_; lean_object* v_res_455_; 
v_t_boxed_454_ = lean_unbox(v_t_451_);
v_res_455_ = l_Lean_Lsp_FileChangeType_ctorElim(v_motive_449_, v_ctorIdx_450_, v_t_boxed_454_, v_h_452_, v_k_453_);
lean_dec(v_k_453_);
lean_dec(v_ctorIdx_450_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Created_elim___redArg(lean_object* v_Created_456_){
_start:
{
lean_inc(v_Created_456_);
return v_Created_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Created_elim___redArg___boxed(lean_object* v_Created_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Lsp_FileChangeType_Created_elim___redArg(v_Created_457_);
lean_dec(v_Created_457_);
return v_res_458_;
}
}
lean_object* l_Lean_Lsp_FileChangeType_Created_elim(lean_object* v_motive_459_, uint8_t v_t_460_, lean_object* v_h_461_, lean_object* v_Created_462_){
_start:
{
lean_inc(v_Created_462_);
return v_Created_462_;
}
}
LEAN_EXPORT void l_Lean_Lsp_FileChangeType_Created_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_460_ = stack[1].m_num;
lean_object* v_Created_462_ = stack[3].m_obj;
lean_object* v_res_463_;
v_res_463_ = l_Lean_Lsp_FileChangeType_Created_elim(lean_box(0), v_t_460_, lean_box(0), v_Created_462_);
stack->m_obj
 = v_res_463_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Created_elim___boxed(lean_object* v_motive_464_, lean_object* v_t_465_, lean_object* v_h_466_, lean_object* v_Created_467_){
_start:
{
uint8_t v_t_boxed_468_; lean_object* v_res_469_; 
v_t_boxed_468_ = lean_unbox(v_t_465_);
v_res_469_ = l_Lean_Lsp_FileChangeType_Created_elim(v_motive_464_, v_t_boxed_468_, v_h_466_, v_Created_467_);
lean_dec(v_Created_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Changed_elim___redArg(lean_object* v_Changed_470_){
_start:
{
lean_inc(v_Changed_470_);
return v_Changed_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Changed_elim___redArg___boxed(lean_object* v_Changed_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_Lsp_FileChangeType_Changed_elim___redArg(v_Changed_471_);
lean_dec(v_Changed_471_);
return v_res_472_;
}
}
lean_object* l_Lean_Lsp_FileChangeType_Changed_elim(lean_object* v_motive_473_, uint8_t v_t_474_, lean_object* v_h_475_, lean_object* v_Changed_476_){
_start:
{
lean_inc(v_Changed_476_);
return v_Changed_476_;
}
}
LEAN_EXPORT void l_Lean_Lsp_FileChangeType_Changed_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_474_ = stack[1].m_num;
lean_object* v_Changed_476_ = stack[3].m_obj;
lean_object* v_res_477_;
v_res_477_ = l_Lean_Lsp_FileChangeType_Changed_elim(lean_box(0), v_t_474_, lean_box(0), v_Changed_476_);
stack->m_obj
 = v_res_477_;
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
lean_object* l_Lean_Lsp_FileChangeType_Deleted_elim(lean_object* v_motive_487_, uint8_t v_t_488_, lean_object* v_h_489_, lean_object* v_Deleted_490_){
_start:
{
lean_inc(v_Deleted_490_);
return v_Deleted_490_;
}
}
LEAN_EXPORT void l_Lean_Lsp_FileChangeType_Deleted_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_488_ = stack[1].m_num;
lean_object* v_Deleted_490_ = stack[3].m_obj;
lean_object* v_res_491_;
v_res_491_ = l_Lean_Lsp_FileChangeType_Deleted_elim(lean_box(0), v_t_488_, lean_box(0), v_Deleted_490_);
stack->m_obj
 = v_res_491_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Deleted_elim___boxed(lean_object* v_motive_492_, lean_object* v_t_493_, lean_object* v_h_494_, lean_object* v_Deleted_495_){
_start:
{
uint8_t v_t_boxed_496_; lean_object* v_res_497_; 
v_t_boxed_496_ = lean_unbox(v_t_493_);
v_res_497_ = l_Lean_Lsp_FileChangeType_Deleted_elim(v_motive_492_, v_t_boxed_496_, v_h_494_, v_Deleted_495_);
lean_dec(v_Deleted_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonFileChangeType___lam__0(lean_object* v_j_508_){
_start:
{
lean_object* v___x_509_; 
lean_inc(v_j_508_);
v___x_509_ = l_Lean_Json_getNat_x3f(v_j_508_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec(v_j_508_);
v_a_510_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_509_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_538_; 
v_a_518_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_538_ == 0)
{
v___x_520_ = v___x_509_;
v_isShared_521_ = v_isSharedCheck_538_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_509_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_538_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_dec_eq(v_a_518_, v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_524_ = lean_unsigned_to_nat(2u);
v___x_525_ = lean_nat_dec_eq(v_a_518_, v___x_524_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_526_ = lean_unsigned_to_nat(3u);
v___x_527_ = lean_nat_dec_eq(v_a_518_, v___x_526_);
lean_dec(v_a_518_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_528_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__0));
v___x_529_ = lean_unsigned_to_nat(80u);
v___x_530_ = l_Lean_Json_pretty(v_j_508_, v___x_529_);
v___x_531_ = lean_string_append(v___x_528_, v___x_530_);
lean_dec_ref(v___x_530_);
if (v_isShared_521_ == 0)
{
lean_ctor_set_tag(v___x_520_, 0);
lean_ctor_set(v___x_520_, 0, v___x_531_);
v___x_533_ = v___x_520_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
else
{
lean_object* v___x_535_; 
lean_del_object(v___x_520_);
lean_dec(v_j_508_);
v___x_535_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__1));
return v___x_535_;
}
}
else
{
lean_object* v___x_536_; 
lean_del_object(v___x_520_);
lean_dec(v_a_518_);
lean_dec(v_j_508_);
v___x_536_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__2));
return v___x_536_;
}
}
else
{
lean_object* v___x_537_; 
lean_del_object(v___x_520_);
lean_dec(v_a_518_);
lean_dec(v_j_508_);
v___x_537_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__3));
return v___x_537_;
}
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_unsigned_to_nat(1u);
v___x_542_ = l_Lean_JsonNumber_fromNat(v___x_541_);
return v___x_542_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0);
v___x_544_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_unsigned_to_nat(2u);
v___x_546_ = l_Lean_JsonNumber_fromNat(v___x_545_);
return v___x_546_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2);
v___x_548_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = lean_unsigned_to_nat(3u);
v___x_550_ = l_Lean_JsonNumber_fromNat(v___x_549_);
return v___x_550_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4);
v___x_552_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
return v___x_552_;
}
}
lean_object* l_Lean_Lsp_instToJsonFileChangeType___lam__0(uint8_t v_x_553_){
_start:
{
switch(v_x_553_)
{
case 0:
{
lean_object* v___x_554_; 
v___x_554_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1);
return v___x_554_;
}
case 1:
{
lean_object* v___x_555_; 
v___x_555_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3);
return v___x_555_;
}
default: 
{
lean_object* v___x_556_; 
v___x_556_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5);
return v___x_556_;
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_instToJsonFileChangeType___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_553_ = stack[0].m_num;
lean_object* v_res_557_;
v_res_557_ = l_Lean_Lsp_instToJsonFileChangeType___lam__0(v_x_553_);
stack->m_obj
 = v_res_557_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileChangeType___lam__0___boxed(lean_object* v_x_558_){
_start:
{
uint8_t v_x_102__boxed_559_; lean_object* v_res_560_; 
v_x_102__boxed_559_ = lean_unbox(v_x_558_);
v_res_560_ = l_Lean_Lsp_instToJsonFileChangeType___lam__0(v_x_102__boxed_559_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0(lean_object* v_j_563_, lean_object* v_k_564_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = l_Lean_Json_getObjValD(v_j_563_, v_k_564_);
lean_inc(v___x_565_);
v___x_566_ = l_Lean_Json_getNat_x3f(v___x_565_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_dec(v___x_565_);
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
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_595_; 
v_a_575_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_595_ == 0)
{
v___x_577_ = v___x_566_;
v_isShared_578_ = v_isSharedCheck_595_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_566_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_595_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = lean_unsigned_to_nat(1u);
v___x_580_ = lean_nat_dec_eq(v_a_575_, v___x_579_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_581_ = lean_unsigned_to_nat(2u);
v___x_582_ = lean_nat_dec_eq(v_a_575_, v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_583_ = lean_unsigned_to_nat(3u);
v___x_584_ = lean_nat_dec_eq(v_a_575_, v___x_583_);
lean_dec(v_a_575_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_585_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__0));
v___x_586_ = lean_unsigned_to_nat(80u);
v___x_587_ = l_Lean_Json_pretty(v___x_565_, v___x_586_);
v___x_588_ = lean_string_append(v___x_585_, v___x_587_);
lean_dec_ref(v___x_587_);
if (v_isShared_578_ == 0)
{
lean_ctor_set_tag(v___x_577_, 0);
lean_ctor_set(v___x_577_, 0, v___x_588_);
v___x_590_ = v___x_577_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
else
{
lean_object* v___x_592_; 
lean_del_object(v___x_577_);
lean_dec(v___x_565_);
v___x_592_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__1));
return v___x_592_;
}
}
else
{
lean_object* v___x_593_; 
lean_del_object(v___x_577_);
lean_dec(v_a_575_);
lean_dec(v___x_565_);
v___x_593_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__2));
return v___x_593_;
}
}
else
{
lean_object* v___x_594_; 
lean_del_object(v___x_577_);
lean_dec(v_a_575_);
lean_dec(v___x_565_);
v___x_594_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__3));
return v___x_594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0___boxed(lean_object* v_j_596_, lean_object* v_k_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0(v_j_596_, v_k_597_);
lean_dec_ref(v_k_597_);
return v_res_598_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2(void){
_start:
{
uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = 1;
v___x_605_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1));
v___x_606_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_605_, v___x_604_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5));
v___x_608_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2);
v___x_609_ = lean_string_append(v___x_608_, v___x_607_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8);
v___x_611_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3);
v___x_612_ = lean_string_append(v___x_611_, v___x_610_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
v___x_614_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4);
v___x_615_ = lean_string_append(v___x_614_, v___x_613_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8(void){
_start:
{
uint8_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = 1;
v___x_620_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__7));
v___x_621_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_620_, v___x_619_);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_622_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8);
v___x_623_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3);
v___x_624_ = lean_string_append(v___x_623_, v___x_622_);
return v___x_624_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
v___x_626_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9);
v___x_627_ = lean_string_append(v___x_626_, v___x_625_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonFileEvent_fromJson(lean_object* v_json_628_){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0));
lean_inc(v_json_628_);
v___x_630_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(v_json_628_, v___x_629_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_640_; 
lean_dec(v_json_628_);
v_a_631_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_640_ == 0)
{
v___x_633_ = v___x_630_;
v_isShared_634_ = v_isSharedCheck_640_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_630_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_640_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_635_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5);
v___x_636_ = lean_string_append(v___x_635_, v_a_631_);
lean_dec(v_a_631_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v___x_636_);
v___x_638_ = v___x_633_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
else
{
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec(v_json_628_);
v_a_641_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_630_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_630_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
lean_ctor_set_tag(v___x_643_, 0);
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_a_649_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_649_);
lean_dec_ref_known(v___x_630_, 1);
v___x_650_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6));
v___x_651_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0(v_json_628_, v___x_650_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_661_; 
lean_dec(v_a_649_);
v_a_652_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_661_ == 0)
{
v___x_654_ = v___x_651_;
v_isShared_655_ = v_isSharedCheck_661_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_661_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_656_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10);
v___x_657_ = lean_string_append(v___x_656_, v_a_652_);
lean_dec(v_a_652_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_657_);
v___x_659_ = v___x_654_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
else
{
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec(v_a_649_);
v_a_662_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_651_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_651_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
lean_ctor_set_tag(v___x_664_, 0);
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_679_; 
v_a_670_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_679_ == 0)
{
v___x_672_ = v___x_651_;
v_isShared_673_ = v_isSharedCheck_679_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_651_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_679_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; uint8_t v___x_675_; lean_object* v___x_677_; 
v___x_674_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_674_, 0, v_a_649_);
v___x_675_ = lean_unbox(v_a_670_);
lean_dec(v_a_670_);
lean_ctor_set_uint8(v___x_674_, sizeof(void*)*1, v___x_675_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_674_);
v___x_677_ = v___x_672_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_674_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileEvent_toJson(lean_object* v_x_682_){
_start:
{
lean_object* v_uri_683_; uint8_t v_type_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___y_692_; 
v_uri_683_ = lean_ctor_get(v_x_682_, 0);
v_type_684_ = lean_ctor_get_uint8(v_x_682_, sizeof(void*)*1);
v___x_685_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0));
lean_inc_ref(v_uri_683_);
v___x_686_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_686_, 0, v_uri_683_);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_685_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = lean_box(0);
v___x_689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_687_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6));
switch(v_type_684_)
{
case 0:
{
lean_object* v___x_700_; 
v___x_700_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1);
v___y_692_ = v___x_700_;
goto v___jp_691_;
}
case 1:
{
lean_object* v___x_701_; 
v___x_701_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3);
v___y_692_ = v___x_701_;
goto v___jp_691_;
}
default: 
{
lean_object* v___x_702_; 
v___x_702_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5);
v___y_692_ = v___x_702_;
goto v___jp_691_;
}
}
v___jp_691_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
lean_inc(v___y_692_);
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_690_);
lean_ctor_set(v___x_693_, 1, v___y_692_);
v___x_694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v___x_688_);
v___x_695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___x_688_);
v___x_696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_689_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2));
v___x_698_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(v___x_696_, v___x_697_);
v___x_699_ = l_Lean_Json_mkObj(v___x_698_);
lean_dec(v___x_698_);
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileEvent_toJson___boxed(lean_object* v_x_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_Lsp_instToJsonFileEvent_toJson(v_x_703_);
lean_dec_ref(v_x_703_);
return v_res_704_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1(size_t v_sz_707_, size_t v_i_708_, lean_object* v_bs_709_){
_start:
{
uint8_t v___x_710_; 
v___x_710_ = lean_usize_dec_lt(v_i_708_, v_sz_707_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; 
v___x_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_711_, 0, v_bs_709_);
return v___x_711_;
}
else
{
lean_object* v_v_712_; lean_object* v___x_713_; 
v_v_712_ = lean_array_uget_borrowed(v_bs_709_, v_i_708_);
lean_inc(v_v_712_);
v___x_713_ = l_Lean_Lsp_instFromJsonFileEvent_fromJson(v_v_712_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec_ref(v_bs_709_);
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_723_; lean_object* v_bs_x27_724_; size_t v___x_725_; size_t v___x_726_; lean_object* v___x_727_; 
v_a_722_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_713_, 1);
v___x_723_ = lean_unsigned_to_nat(0u);
v_bs_x27_724_ = lean_array_uset(v_bs_709_, v_i_708_, v___x_723_);
v___x_725_ = ((size_t)1ULL);
v___x_726_ = lean_usize_add(v_i_708_, v___x_725_);
v___x_727_ = lean_array_uset(v_bs_x27_724_, v_i_708_, v_a_722_);
v_i_708_ = v___x_726_;
v_bs_709_ = v___x_727_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_707_ = stack[0].m_num;
size_t v_i_708_ = stack[1].m_num;
lean_object* v_bs_709_ = stack[2].m_obj;
lean_object* v_res_729_;
v_res_729_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1(v_sz_707_, v_i_708_, v_bs_709_);
stack->m_obj
 = v_res_729_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_730_, lean_object* v_i_731_, lean_object* v_bs_732_){
_start:
{
size_t v_sz_boxed_733_; size_t v_i_boxed_734_; lean_object* v_res_735_; 
v_sz_boxed_733_ = lean_unbox_usize(v_sz_730_);
lean_dec(v_sz_730_);
v_i_boxed_734_ = lean_unbox_usize(v_i_731_);
lean_dec(v_i_731_);
v_res_735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_733_, v_i_boxed_734_, v_bs_732_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0(lean_object* v_x_736_){
_start:
{
if (lean_obj_tag(v_x_736_) == 4)
{
lean_object* v_elems_737_; size_t v_sz_738_; size_t v___x_739_; lean_object* v___x_740_; 
v_elems_737_ = lean_ctor_get(v_x_736_, 0);
lean_inc_ref(v_elems_737_);
lean_dec_ref_known(v_x_736_, 1);
v_sz_738_ = lean_array_size(v_elems_737_);
v___x_739_ = ((size_t)0ULL);
v___x_740_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1(v_sz_738_, v___x_739_, v_elems_737_);
return v___x_740_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_741_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0));
v___x_742_ = lean_unsigned_to_nat(80u);
v___x_743_ = l_Lean_Json_pretty(v_x_736_, v___x_742_);
v___x_744_ = lean_string_append(v___x_741_, v___x_743_);
lean_dec_ref(v___x_743_);
v___x_745_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1));
v___x_746_ = lean_string_append(v___x_744_, v___x_745_);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0(lean_object* v_j_748_, lean_object* v_k_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = l_Lean_Json_getObjValD(v_j_748_, v_k_749_);
v___x_751_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0(v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0___boxed(lean_object* v_j_752_, lean_object* v_k_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0(v_j_752_, v_k_753_);
lean_dec_ref(v_k_753_);
return v_res_754_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_761_ = 1;
v___x_762_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2));
v___x_763_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_762_, v___x_761_);
return v___x_763_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_764_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5));
v___x_765_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3);
v___x_766_ = lean_string_append(v___x_765_, v___x_764_);
return v___x_766_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_769_ = 1;
v___x_770_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__5));
v___x_771_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_770_, v___x_769_);
return v___x_771_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_772_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6);
v___x_773_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4);
v___x_774_ = lean_string_append(v___x_773_, v___x_772_);
return v___x_774_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_775_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
v___x_776_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7);
v___x_777_ = lean_string_append(v___x_776_, v___x_775_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson(lean_object* v_json_778_){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0));
v___x_780_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0(v_json_778_, v___x_779_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_790_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_790_ == 0)
{
v___x_783_ = v___x_780_;
v_isShared_784_ = v_isSharedCheck_790_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_780_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_790_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_785_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8);
v___x_786_ = lean_string_append(v___x_785_, v_a_781_);
lean_dec(v_a_781_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_786_);
v___x_788_ = v___x_783_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
else
{
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
v_a_791_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_780_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_780_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set_tag(v___x_793_, 0);
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
v_a_799_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_780_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_780_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0(size_t v_sz_809_, size_t v_i_810_, lean_object* v_bs_811_){
_start:
{
uint8_t v___x_812_; 
v___x_812_ = lean_usize_dec_lt(v_i_810_, v_sz_809_);
if (v___x_812_ == 0)
{
return v_bs_811_;
}
else
{
lean_object* v_v_813_; lean_object* v___x_814_; lean_object* v_bs_x27_815_; lean_object* v___x_816_; size_t v___x_817_; size_t v___x_818_; lean_object* v___x_819_; 
v_v_813_ = lean_array_uget(v_bs_811_, v_i_810_);
v___x_814_ = lean_unsigned_to_nat(0u);
v_bs_x27_815_ = lean_array_uset(v_bs_811_, v_i_810_, v___x_814_);
v___x_816_ = l_Lean_Lsp_instToJsonFileEvent_toJson(v_v_813_);
lean_dec(v_v_813_);
v___x_817_ = ((size_t)1ULL);
v___x_818_ = lean_usize_add(v_i_810_, v___x_817_);
v___x_819_ = lean_array_uset(v_bs_x27_815_, v_i_810_, v___x_816_);
v_i_810_ = v___x_818_;
v_bs_811_ = v___x_819_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_809_ = stack[0].m_num;
size_t v_i_810_ = stack[1].m_num;
lean_object* v_bs_811_ = stack[2].m_obj;
lean_object* v_res_821_;
v_res_821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0(v_sz_809_, v_i_810_, v_bs_811_);
stack->m_obj
 = v_res_821_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_822_, lean_object* v_i_823_, lean_object* v_bs_824_){
_start:
{
size_t v_sz_boxed_825_; size_t v_i_boxed_826_; lean_object* v_res_827_; 
v_sz_boxed_825_ = lean_unbox_usize(v_sz_822_);
lean_dec(v_sz_822_);
v_i_boxed_826_ = lean_unbox_usize(v_i_823_);
lean_dec(v_i_823_);
v_res_827_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0(v_sz_boxed_825_, v_i_boxed_826_, v_bs_824_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0(lean_object* v_a_828_){
_start:
{
size_t v_sz_829_; size_t v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v_sz_829_ = lean_array_size(v_a_828_);
v___x_830_ = ((size_t)0ULL);
v___x_831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0(v_sz_829_, v___x_830_, v_a_828_);
v___x_832_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson(lean_object* v_x_833_){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_834_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0));
v___x_835_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0(v_x_833_);
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_834_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = lean_box(0);
v___x_838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_836_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
lean_ctor_set(v___x_839_, 1, v___x_837_);
v___x_840_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2));
v___x_841_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(v___x_839_, v___x_840_);
v___x_842_ = l_Lean_Json_mkObj(v___x_841_);
lean_dec(v___x_841_);
return v___x_842_;
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Workspace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
