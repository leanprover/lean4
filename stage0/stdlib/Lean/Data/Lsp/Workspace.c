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
lean_object* v_a_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v_a_94_ = lean_ctor_get(v___x_83_, 0);
lean_inc(v_a_94_);
lean_dec_ref_known(v___x_83_, 1);
v___x_95_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1));
v___x_96_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(v_json_81_, v___x_95_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_106_; 
lean_dec(v_a_94_);
v_a_97_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_106_ == 0)
{
v___x_99_ = v___x_96_;
v_isShared_100_ = v_isSharedCheck_106_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_96_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_106_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_104_; 
v___x_101_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15);
v___x_102_ = lean_string_append(v___x_101_, v_a_97_);
lean_dec(v_a_97_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_102_);
v___x_104_ = v___x_99_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_102_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
else
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_115_; 
v_a_107_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_115_ == 0)
{
v___x_109_ = v___x_96_;
v_isShared_110_ = v_isSharedCheck_115_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_96_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_115_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_113_; 
v___x_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_111_, 0, v_a_94_);
lean_ctor_set(v___x_111_, 1, v_a_107_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_111_);
v___x_113_ = v___x_109_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0(lean_object* v_x_120_){
_start:
{
if (lean_obj_tag(v_x_120_) == 0)
{
lean_object* v___x_121_; 
v___x_121_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0___closed__0));
return v___x_121_;
}
else
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_Json_getNat_x3f(v_x_120_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_139_; 
v_a_131_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_139_ == 0)
{
v___x_133_ = v___x_122_;
v_isShared_134_ = v_isSharedCheck_139_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_122_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_139_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_135_, 0, v_a_131_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v___x_135_);
v___x_137_ = v___x_133_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0(lean_object* v_j_140_, lean_object* v_k_141_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = l_Lean_Json_getObjValD(v_j_140_, v_k_141_);
v___x_143_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0(v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0___boxed(lean_object* v_j_144_, lean_object* v_k_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0(v_j_144_, v_k_145_);
lean_dec_ref(v_k_145_);
return v_res_146_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3(void){
_start:
{
uint8_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_153_ = 1;
v___x_154_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2));
v___x_155_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_154_, v___x_153_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5));
v___x_157_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3);
v___x_158_ = lean_string_append(v___x_157_, v___x_156_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6(void){
_start:
{
uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = 1;
v___x_162_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__5));
v___x_163_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_162_, v___x_161_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6);
v___x_165_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4);
v___x_166_ = lean_string_append(v___x_165_, v___x_164_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
v___x_168_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7);
v___x_169_ = lean_string_append(v___x_168_, v___x_167_);
return v___x_169_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12(void){
_start:
{
uint8_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = 1;
v___x_175_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__11));
v___x_176_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_175_, v___x_174_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12);
v___x_178_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4);
v___x_179_ = lean_string_append(v___x_178_, v___x_177_);
return v___x_179_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
v___x_181_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13);
v___x_182_ = lean_string_append(v___x_181_, v___x_180_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson(lean_object* v_json_183_){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__0));
lean_inc(v_json_183_);
v___x_185_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(v_json_183_, v___x_184_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_195_; 
lean_dec(v_json_183_);
v_a_186_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_195_ == 0)
{
v___x_188_ = v___x_185_;
v_isShared_189_ = v_isSharedCheck_195_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_185_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_195_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_190_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8);
v___x_191_ = lean_string_append(v___x_190_, v_a_186_);
lean_dec(v_a_186_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_191_);
v___x_193_ = v___x_188_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_a_196_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_196_);
lean_dec_ref_known(v___x_185_, 1);
v___x_197_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__9));
v___x_198_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0(v_json_183_, v___x_197_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_208_; 
lean_dec(v_a_196_);
v_a_199_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_208_ == 0)
{
v___x_201_ = v___x_198_;
v_isShared_202_ = v_isSharedCheck_208_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_198_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_208_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_203_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14, &l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14);
v___x_204_ = lean_string_append(v___x_203_, v_a_199_);
lean_dec(v_a_199_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___x_204_);
v___x_206_ = v___x_201_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_204_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_217_; 
v_a_209_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_217_ == 0)
{
v___x_211_ = v___x_198_;
v_isShared_212_ = v_isSharedCheck_217_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_198_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_217_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v_a_196_);
lean_ctor_set(v___x_213_, 1, v_a_209_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_213_);
v___x_215_ = v___x_211_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonFileSystemWatcher_toJson_spec__0(lean_object* v_k_220_, lean_object* v_x_221_){
_start:
{
if (lean_obj_tag(v_x_221_) == 0)
{
lean_object* v___x_222_; 
lean_dec_ref(v_k_220_);
v___x_222_ = lean_box(0);
return v___x_222_;
}
else
{
lean_object* v_val_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_234_; 
v_val_223_ = lean_ctor_get(v_x_221_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v_x_221_);
if (v_isSharedCheck_234_ == 0)
{
v___x_225_ = v_x_221_;
v_isShared_226_ = v_isSharedCheck_234_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_val_223_);
lean_dec(v_x_221_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_234_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_227_ = l_Lean_JsonNumber_fromNat(v_val_223_);
if (v_isShared_226_ == 0)
{
lean_ctor_set_tag(v___x_225_, 2);
lean_ctor_set(v___x_225_, 0, v___x_227_);
v___x_229_ = v___x_225_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_227_);
v___x_229_ = v_reuseFailAlloc_233_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_230_, 0, v_k_220_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = lean_box(0);
v___x_232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_230_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
return v___x_232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileSystemWatcher_toJson(lean_object* v_x_235_){
_start:
{
lean_object* v_globPattern_236_; lean_object* v_kind_x3f_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_255_; 
v_globPattern_236_ = lean_ctor_get(v_x_235_, 0);
v_kind_x3f_237_ = lean_ctor_get(v_x_235_, 1);
v_isSharedCheck_255_ = !lean_is_exclusive(v_x_235_);
if (v_isSharedCheck_255_ == 0)
{
v___x_239_ = v_x_235_;
v_isShared_240_ = v_isSharedCheck_255_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_kind_x3f_237_);
lean_inc(v_globPattern_236_);
lean_dec(v_x_235_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_255_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_241_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__0));
v___x_242_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_242_, 0, v_globPattern_236_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___x_242_);
lean_ctor_set(v___x_239_, 0, v___x_241_);
v___x_244_ = v___x_239_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v___x_242_);
v___x_244_ = v_reuseFailAlloc_254_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_245_ = lean_box(0);
v___x_246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_244_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__9));
v___x_248_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonFileSystemWatcher_toJson_spec__0(v___x_247_, v_kind_x3f_237_);
v___x_249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___x_245_);
v___x_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_246_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2));
v___x_252_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(v___x_250_, v___x_251_);
v___x_253_ = l_Lean_Json_mkObj(v___x_252_);
lean_dec(v___x_252_);
return v___x_253_;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_FileSystemWatcher_create(void){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = lean_unsigned_to_nat(1u);
return v___x_258_;
}
}
static lean_object* _init_l_Lean_Lsp_FileSystemWatcher_change(void){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = lean_unsigned_to_nat(2u);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_Lsp_FileSystemWatcher_delete(void){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = lean_unsigned_to_nat(4u);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1(size_t v_sz_261_, size_t v_i_262_, lean_object* v_bs_263_){
_start:
{
uint8_t v___x_264_; 
v___x_264_ = lean_usize_dec_lt(v_i_262_, v_sz_261_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
v___x_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_265_, 0, v_bs_263_);
return v___x_265_;
}
else
{
lean_object* v_v_266_; lean_object* v___x_267_; 
v_v_266_ = lean_array_uget_borrowed(v_bs_263_, v_i_262_);
lean_inc(v_v_266_);
v___x_267_ = l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson(v_v_266_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_275_; 
lean_dec_ref(v_bs_263_);
v_a_268_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_275_ == 0)
{
v___x_270_ = v___x_267_;
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_267_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_273_; 
if (v_isShared_271_ == 0)
{
v___x_273_ = v___x_270_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_268_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_277_; lean_object* v_bs_x27_278_; size_t v___x_279_; size_t v___x_280_; lean_object* v___x_281_; 
v_a_276_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v___x_267_, 1);
v___x_277_ = lean_unsigned_to_nat(0u);
v_bs_x27_278_ = lean_array_uset(v_bs_263_, v_i_262_, v___x_277_);
v___x_279_ = ((size_t)1ULL);
v___x_280_ = lean_usize_add(v_i_262_, v___x_279_);
v___x_281_ = lean_array_uset(v_bs_x27_278_, v_i_262_, v_a_276_);
v_i_262_ = v___x_280_;
v_bs_263_ = v___x_281_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_283_, lean_object* v_i_284_, lean_object* v_bs_285_){
_start:
{
size_t v_sz_boxed_286_; size_t v_i_boxed_287_; lean_object* v_res_288_; 
v_sz_boxed_286_ = lean_unbox_usize(v_sz_283_);
lean_dec(v_sz_283_);
v_i_boxed_287_ = lean_unbox_usize(v_i_284_);
lean_dec(v_i_284_);
v_res_288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_286_, v_i_boxed_287_, v_bs_285_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0(lean_object* v_x_291_){
_start:
{
if (lean_obj_tag(v_x_291_) == 4)
{
lean_object* v_elems_292_; size_t v_sz_293_; size_t v___x_294_; lean_object* v___x_295_; 
v_elems_292_ = lean_ctor_get(v_x_291_, 0);
lean_inc_ref(v_elems_292_);
lean_dec_ref_known(v_x_291_, 1);
v_sz_293_ = lean_array_size(v_elems_292_);
v___x_294_ = ((size_t)0ULL);
v___x_295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1(v_sz_293_, v___x_294_, v_elems_292_);
return v___x_295_;
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_296_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0));
v___x_297_ = lean_unsigned_to_nat(80u);
v___x_298_ = l_Lean_Json_pretty(v_x_291_, v___x_297_);
v___x_299_ = lean_string_append(v___x_296_, v___x_298_);
lean_dec_ref(v___x_298_);
v___x_300_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1));
v___x_301_ = lean_string_append(v___x_299_, v___x_300_);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0(lean_object* v_j_303_, lean_object* v_k_304_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = l_Lean_Json_getObjValD(v_j_303_, v_k_304_);
v___x_306_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0(v___x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0___boxed(lean_object* v_j_307_, lean_object* v_k_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0(v_j_307_, v_k_308_);
lean_dec_ref(v_k_308_);
return v_res_309_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3(void){
_start:
{
uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = 1;
v___x_317_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2));
v___x_318_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_317_, v___x_316_);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5));
v___x_320_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3);
v___x_321_ = lean_string_append(v___x_320_, v___x_319_);
return v___x_321_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6(void){
_start:
{
uint8_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_324_ = 1;
v___x_325_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__5));
v___x_326_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_325_, v___x_324_);
return v___x_326_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_327_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6);
v___x_328_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4);
v___x_329_ = lean_string_append(v___x_328_, v___x_327_);
return v___x_329_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_330_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
v___x_331_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7);
v___x_332_ = lean_string_append(v___x_331_, v___x_330_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson(lean_object* v_json_333_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0));
v___x_335_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0(v_json_333_, v___x_334_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_345_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_345_ == 0)
{
v___x_338_ = v___x_335_;
v_isShared_339_ = v_isSharedCheck_345_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_345_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_340_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8);
v___x_341_ = lean_string_append(v___x_340_, v_a_336_);
lean_dec(v_a_336_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_341_);
v___x_343_ = v___x_338_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
v_a_346_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_335_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_335_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0(size_t v_sz_356_, size_t v_i_357_, lean_object* v_bs_358_){
_start:
{
uint8_t v___x_359_; 
v___x_359_ = lean_usize_dec_lt(v_i_357_, v_sz_356_);
if (v___x_359_ == 0)
{
return v_bs_358_;
}
else
{
lean_object* v_v_360_; lean_object* v___x_361_; lean_object* v_bs_x27_362_; lean_object* v___x_363_; size_t v___x_364_; size_t v___x_365_; lean_object* v___x_366_; 
v_v_360_ = lean_array_uget(v_bs_358_, v_i_357_);
v___x_361_ = lean_unsigned_to_nat(0u);
v_bs_x27_362_ = lean_array_uset(v_bs_358_, v_i_357_, v___x_361_);
v___x_363_ = l_Lean_Lsp_instToJsonFileSystemWatcher_toJson(v_v_360_);
v___x_364_ = ((size_t)1ULL);
v___x_365_ = lean_usize_add(v_i_357_, v___x_364_);
v___x_366_ = lean_array_uset(v_bs_x27_362_, v_i_357_, v___x_363_);
v_i_357_ = v___x_365_;
v_bs_358_ = v___x_366_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0___boxed(lean_object* v_sz_368_, lean_object* v_i_369_, lean_object* v_bs_370_){
_start:
{
size_t v_sz_boxed_371_; size_t v_i_boxed_372_; lean_object* v_res_373_; 
v_sz_boxed_371_ = lean_unbox_usize(v_sz_368_);
lean_dec(v_sz_368_);
v_i_boxed_372_ = lean_unbox_usize(v_i_369_);
lean_dec(v_i_369_);
v_res_373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0(v_sz_boxed_371_, v_i_boxed_372_, v_bs_370_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0(lean_object* v_a_374_){
_start:
{
size_t v_sz_375_; size_t v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_sz_375_ = lean_array_size(v_a_374_);
v___x_376_ = ((size_t)0ULL);
v___x_377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0(v_sz_375_, v___x_376_, v_a_374_);
v___x_378_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson(lean_object* v_x_379_){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_380_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0));
v___x_381_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0(v_x_379_);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v___x_383_ = lean_box(0);
v___x_384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_382_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v___x_383_);
v___x_386_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2));
v___x_387_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(v___x_385_, v___x_386_);
v___x_388_ = l_Lean_Json_mkObj(v___x_387_);
lean_dec(v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorIdx___impl(uint8_t v_x_391_){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_box(v_x_391_);
v___x_393_ = lean_obj_tag_nat(v___x_392_);
lean_dec(v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorIdx___impl___boxed(lean_object* v_x_394_){
_start:
{
uint8_t v_x_4__boxed_395_; lean_object* v_res_396_; 
v_x_4__boxed_395_ = lean_unbox(v_x_394_);
v_res_396_ = l_Lean_Lsp_FileChangeType_ctorIdx___impl(v_x_4__boxed_395_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorElim___redArg(lean_object* v_k_397_){
_start:
{
lean_inc(v_k_397_);
return v_k_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorElim___redArg___boxed(lean_object* v_k_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Lsp_FileChangeType_ctorElim___redArg(v_k_398_);
lean_dec(v_k_398_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorElim(lean_object* v_motive_400_, lean_object* v_ctorIdx_401_, uint8_t v_t_402_, lean_object* v_h_403_, lean_object* v_k_404_){
_start:
{
lean_inc(v_k_404_);
return v_k_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_ctorElim___boxed(lean_object* v_motive_405_, lean_object* v_ctorIdx_406_, lean_object* v_t_407_, lean_object* v_h_408_, lean_object* v_k_409_){
_start:
{
uint8_t v_t_boxed_410_; lean_object* v_res_411_; 
v_t_boxed_410_ = lean_unbox(v_t_407_);
v_res_411_ = l_Lean_Lsp_FileChangeType_ctorElim(v_motive_405_, v_ctorIdx_406_, v_t_boxed_410_, v_h_408_, v_k_409_);
lean_dec(v_k_409_);
lean_dec(v_ctorIdx_406_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Created_elim___redArg(lean_object* v_Created_412_){
_start:
{
lean_inc(v_Created_412_);
return v_Created_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Created_elim___redArg___boxed(lean_object* v_Created_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Lsp_FileChangeType_Created_elim___redArg(v_Created_413_);
lean_dec(v_Created_413_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Created_elim(lean_object* v_motive_415_, uint8_t v_t_416_, lean_object* v_h_417_, lean_object* v_Created_418_){
_start:
{
lean_inc(v_Created_418_);
return v_Created_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Created_elim___boxed(lean_object* v_motive_419_, lean_object* v_t_420_, lean_object* v_h_421_, lean_object* v_Created_422_){
_start:
{
uint8_t v_t_boxed_423_; lean_object* v_res_424_; 
v_t_boxed_423_ = lean_unbox(v_t_420_);
v_res_424_ = l_Lean_Lsp_FileChangeType_Created_elim(v_motive_419_, v_t_boxed_423_, v_h_421_, v_Created_422_);
lean_dec(v_Created_422_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Changed_elim___redArg(lean_object* v_Changed_425_){
_start:
{
lean_inc(v_Changed_425_);
return v_Changed_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Changed_elim___redArg___boxed(lean_object* v_Changed_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Lsp_FileChangeType_Changed_elim___redArg(v_Changed_426_);
lean_dec(v_Changed_426_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Changed_elim(lean_object* v_motive_428_, uint8_t v_t_429_, lean_object* v_h_430_, lean_object* v_Changed_431_){
_start:
{
lean_inc(v_Changed_431_);
return v_Changed_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Changed_elim___boxed(lean_object* v_motive_432_, lean_object* v_t_433_, lean_object* v_h_434_, lean_object* v_Changed_435_){
_start:
{
uint8_t v_t_boxed_436_; lean_object* v_res_437_; 
v_t_boxed_436_ = lean_unbox(v_t_433_);
v_res_437_ = l_Lean_Lsp_FileChangeType_Changed_elim(v_motive_432_, v_t_boxed_436_, v_h_434_, v_Changed_435_);
lean_dec(v_Changed_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Deleted_elim___redArg(lean_object* v_Deleted_438_){
_start:
{
lean_inc(v_Deleted_438_);
return v_Deleted_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Deleted_elim___redArg___boxed(lean_object* v_Deleted_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Lsp_FileChangeType_Deleted_elim___redArg(v_Deleted_439_);
lean_dec(v_Deleted_439_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Deleted_elim(lean_object* v_motive_441_, uint8_t v_t_442_, lean_object* v_h_443_, lean_object* v_Deleted_444_){
_start:
{
lean_inc(v_Deleted_444_);
return v_Deleted_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_FileChangeType_Deleted_elim___boxed(lean_object* v_motive_445_, lean_object* v_t_446_, lean_object* v_h_447_, lean_object* v_Deleted_448_){
_start:
{
uint8_t v_t_boxed_449_; lean_object* v_res_450_; 
v_t_boxed_449_ = lean_unbox(v_t_446_);
v_res_450_ = l_Lean_Lsp_FileChangeType_Deleted_elim(v_motive_445_, v_t_boxed_449_, v_h_447_, v_Deleted_448_);
lean_dec(v_Deleted_448_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonFileChangeType___lam__0(lean_object* v_j_461_){
_start:
{
lean_object* v___x_462_; 
lean_inc(v_j_461_);
v___x_462_ = l_Lean_Json_getNat_x3f(v_j_461_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec(v_j_461_);
v_a_463_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_462_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_462_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_491_; 
v_a_471_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_491_ == 0)
{
v___x_473_ = v___x_462_;
v_isShared_474_ = v_isSharedCheck_491_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_462_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_491_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_475_ = lean_unsigned_to_nat(1u);
v___x_476_ = lean_nat_dec_eq(v_a_471_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_477_ = lean_unsigned_to_nat(2u);
v___x_478_ = lean_nat_dec_eq(v_a_471_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = lean_unsigned_to_nat(3u);
v___x_480_ = lean_nat_dec_eq(v_a_471_, v___x_479_);
lean_dec(v_a_471_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_481_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__0));
v___x_482_ = lean_unsigned_to_nat(80u);
v___x_483_ = l_Lean_Json_pretty(v_j_461_, v___x_482_);
v___x_484_ = lean_string_append(v___x_481_, v___x_483_);
lean_dec_ref(v___x_483_);
if (v_isShared_474_ == 0)
{
lean_ctor_set_tag(v___x_473_, 0);
lean_ctor_set(v___x_473_, 0, v___x_484_);
v___x_486_ = v___x_473_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
else
{
lean_object* v___x_488_; 
lean_del_object(v___x_473_);
lean_dec(v_j_461_);
v___x_488_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__1));
return v___x_488_;
}
}
else
{
lean_object* v___x_489_; 
lean_del_object(v___x_473_);
lean_dec(v_a_471_);
lean_dec(v_j_461_);
v___x_489_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__2));
return v___x_489_;
}
}
else
{
lean_object* v___x_490_; 
lean_del_object(v___x_473_);
lean_dec(v_a_471_);
lean_dec(v_j_461_);
v___x_490_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__3));
return v___x_490_;
}
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = l_Lean_JsonNumber_fromNat(v___x_494_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0);
v___x_497_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_unsigned_to_nat(2u);
v___x_499_ = l_Lean_JsonNumber_fromNat(v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2);
v___x_501_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_unsigned_to_nat(3u);
v___x_503_ = l_Lean_JsonNumber_fromNat(v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4);
v___x_505_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileChangeType___lam__0(uint8_t v_x_506_){
_start:
{
switch(v_x_506_)
{
case 0:
{
lean_object* v___x_507_; 
v___x_507_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1);
return v___x_507_;
}
case 1:
{
lean_object* v___x_508_; 
v___x_508_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3);
return v___x_508_;
}
default: 
{
lean_object* v___x_509_; 
v___x_509_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5);
return v___x_509_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileChangeType___lam__0___boxed(lean_object* v_x_510_){
_start:
{
uint8_t v_x_102__boxed_511_; lean_object* v_res_512_; 
v_x_102__boxed_511_ = lean_unbox(v_x_510_);
v_res_512_ = l_Lean_Lsp_instToJsonFileChangeType___lam__0(v_x_102__boxed_511_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0(lean_object* v_j_515_, lean_object* v_k_516_){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = l_Lean_Json_getObjValD(v_j_515_, v_k_516_);
lean_inc(v___x_517_);
v___x_518_ = l_Lean_Json_getNat_x3f(v___x_517_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_dec(v___x_517_);
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_547_; 
v_a_527_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_547_ == 0)
{
v___x_529_ = v___x_518_;
v_isShared_530_ = v_isSharedCheck_547_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_518_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_547_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_531_ = lean_unsigned_to_nat(1u);
v___x_532_ = lean_nat_dec_eq(v_a_527_, v___x_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = lean_unsigned_to_nat(2u);
v___x_534_ = lean_nat_dec_eq(v_a_527_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_535_ = lean_unsigned_to_nat(3u);
v___x_536_ = lean_nat_dec_eq(v_a_527_, v___x_535_);
lean_dec(v_a_527_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
v___x_537_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__0));
v___x_538_ = lean_unsigned_to_nat(80u);
v___x_539_ = l_Lean_Json_pretty(v___x_517_, v___x_538_);
v___x_540_ = lean_string_append(v___x_537_, v___x_539_);
lean_dec_ref(v___x_539_);
if (v_isShared_530_ == 0)
{
lean_ctor_set_tag(v___x_529_, 0);
lean_ctor_set(v___x_529_, 0, v___x_540_);
v___x_542_ = v___x_529_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
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
lean_object* v___x_544_; 
lean_del_object(v___x_529_);
lean_dec(v___x_517_);
v___x_544_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__1));
return v___x_544_;
}
}
else
{
lean_object* v___x_545_; 
lean_del_object(v___x_529_);
lean_dec(v_a_527_);
lean_dec(v___x_517_);
v___x_545_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__2));
return v___x_545_;
}
}
else
{
lean_object* v___x_546_; 
lean_del_object(v___x_529_);
lean_dec(v_a_527_);
lean_dec(v___x_517_);
v___x_546_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__3));
return v___x_546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0___boxed(lean_object* v_j_548_, lean_object* v_k_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0(v_j_548_, v_k_549_);
lean_dec_ref(v_k_549_);
return v_res_550_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2(void){
_start:
{
uint8_t v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = 1;
v___x_557_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1));
v___x_558_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_557_, v___x_556_);
return v___x_558_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5));
v___x_560_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2);
v___x_561_ = lean_string_append(v___x_560_, v___x_559_);
return v___x_561_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_562_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8);
v___x_563_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3);
v___x_564_ = lean_string_append(v___x_563_, v___x_562_);
return v___x_564_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_565_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
v___x_566_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4);
v___x_567_ = lean_string_append(v___x_566_, v___x_565_);
return v___x_567_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8(void){
_start:
{
uint8_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = 1;
v___x_572_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__7));
v___x_573_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_572_, v___x_571_);
return v___x_573_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8);
v___x_575_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3);
v___x_576_ = lean_string_append(v___x_575_, v___x_574_);
return v___x_576_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_577_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
v___x_578_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9);
v___x_579_ = lean_string_append(v___x_578_, v___x_577_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonFileEvent_fromJson(lean_object* v_json_580_){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0));
lean_inc(v_json_580_);
v___x_582_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(v_json_580_, v___x_581_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_592_; 
lean_dec(v_json_580_);
v_a_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_592_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_592_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_592_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_587_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5);
v___x_588_ = lean_string_append(v___x_587_, v_a_583_);
lean_dec(v_a_583_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_588_);
v___x_590_ = v___x_585_;
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
}
else
{
lean_object* v_a_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_a_593_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_593_);
lean_dec_ref_known(v___x_582_, 1);
v___x_594_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6));
v___x_595_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0(v_json_580_, v___x_594_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_605_; 
lean_dec(v_a_593_);
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_605_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_605_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_605_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_600_ = lean_obj_once(&l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10, &l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10);
v___x_601_ = lean_string_append(v___x_600_, v_a_596_);
lean_dec(v_a_596_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_601_);
v___x_603_ = v___x_598_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_615_; 
v_a_606_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_615_ == 0)
{
v___x_608_ = v___x_595_;
v_isShared_609_ = v_isSharedCheck_615_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_595_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_615_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; uint8_t v___x_611_; lean_object* v___x_613_; 
v___x_610_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_610_, 0, v_a_593_);
v___x_611_ = lean_unbox(v_a_606_);
lean_dec(v_a_606_);
lean_ctor_set_uint8(v___x_610_, sizeof(void*)*1, v___x_611_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_610_);
v___x_613_ = v___x_608_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_610_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileEvent_toJson(lean_object* v_x_618_){
_start:
{
lean_object* v_uri_619_; uint8_t v_type_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___y_628_; 
v_uri_619_ = lean_ctor_get(v_x_618_, 0);
v_type_620_ = lean_ctor_get_uint8(v_x_618_, sizeof(void*)*1);
v___x_621_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0));
lean_inc_ref(v_uri_619_);
v___x_622_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_622_, 0, v_uri_619_);
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = lean_box(0);
v___x_625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = ((lean_object*)(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6));
switch(v_type_620_)
{
case 0:
{
lean_object* v___x_636_; 
v___x_636_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1);
v___y_628_ = v___x_636_;
goto v___jp_627_;
}
case 1:
{
lean_object* v___x_637_; 
v___x_637_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3);
v___y_628_ = v___x_637_;
goto v___jp_627_;
}
default: 
{
lean_object* v___x_638_; 
v___x_638_ = lean_obj_once(&l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5, &l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5);
v___y_628_ = v___x_638_;
goto v___jp_627_;
}
}
v___jp_627_:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
lean_inc(v___y_628_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_626_);
lean_ctor_set(v___x_629_, 1, v___y_628_);
v___x_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v___x_624_);
v___x_631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v___x_624_);
v___x_632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_625_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2));
v___x_634_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(v___x_632_, v___x_633_);
v___x_635_ = l_Lean_Json_mkObj(v___x_634_);
lean_dec(v___x_634_);
return v___x_635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonFileEvent_toJson___boxed(lean_object* v_x_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_Lsp_instToJsonFileEvent_toJson(v_x_639_);
lean_dec_ref(v_x_639_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1(size_t v_sz_643_, size_t v_i_644_, lean_object* v_bs_645_){
_start:
{
uint8_t v___x_646_; 
v___x_646_ = lean_usize_dec_lt(v_i_644_, v_sz_643_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; 
v___x_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_647_, 0, v_bs_645_);
return v___x_647_;
}
else
{
lean_object* v_v_648_; lean_object* v___x_649_; 
v_v_648_ = lean_array_uget_borrowed(v_bs_645_, v_i_644_);
lean_inc(v_v_648_);
v___x_649_ = l_Lean_Lsp_instFromJsonFileEvent_fromJson(v_v_648_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec_ref(v_bs_645_);
v_a_650_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
else
{
lean_object* v_a_658_; lean_object* v___x_659_; lean_object* v_bs_x27_660_; size_t v___x_661_; size_t v___x_662_; lean_object* v___x_663_; 
v_a_658_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v___x_649_, 1);
v___x_659_ = lean_unsigned_to_nat(0u);
v_bs_x27_660_ = lean_array_uset(v_bs_645_, v_i_644_, v___x_659_);
v___x_661_ = ((size_t)1ULL);
v___x_662_ = lean_usize_add(v_i_644_, v___x_661_);
v___x_663_ = lean_array_uset(v_bs_x27_660_, v_i_644_, v_a_658_);
v_i_644_ = v___x_662_;
v_bs_645_ = v___x_663_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_665_, lean_object* v_i_666_, lean_object* v_bs_667_){
_start:
{
size_t v_sz_boxed_668_; size_t v_i_boxed_669_; lean_object* v_res_670_; 
v_sz_boxed_668_ = lean_unbox_usize(v_sz_665_);
lean_dec(v_sz_665_);
v_i_boxed_669_ = lean_unbox_usize(v_i_666_);
lean_dec(v_i_666_);
v_res_670_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_668_, v_i_boxed_669_, v_bs_667_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0(lean_object* v_x_671_){
_start:
{
if (lean_obj_tag(v_x_671_) == 4)
{
lean_object* v_elems_672_; size_t v_sz_673_; size_t v___x_674_; lean_object* v___x_675_; 
v_elems_672_ = lean_ctor_get(v_x_671_, 0);
lean_inc_ref(v_elems_672_);
lean_dec_ref_known(v_x_671_, 1);
v_sz_673_ = lean_array_size(v_elems_672_);
v___x_674_ = ((size_t)0ULL);
v___x_675_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1(v_sz_673_, v___x_674_, v_elems_672_);
return v___x_675_;
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_676_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0));
v___x_677_ = lean_unsigned_to_nat(80u);
v___x_678_ = l_Lean_Json_pretty(v_x_671_, v___x_677_);
v___x_679_ = lean_string_append(v___x_676_, v___x_678_);
lean_dec_ref(v___x_678_);
v___x_680_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1));
v___x_681_ = lean_string_append(v___x_679_, v___x_680_);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
return v___x_682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0(lean_object* v_j_683_, lean_object* v_k_684_){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = l_Lean_Json_getObjValD(v_j_683_, v_k_684_);
v___x_686_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0(v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0___boxed(lean_object* v_j_687_, lean_object* v_k_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0(v_j_687_, v_k_688_);
lean_dec_ref(v_k_688_);
return v_res_689_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = 1;
v___x_697_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2));
v___x_698_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_697_, v___x_696_);
return v___x_698_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5));
v___x_700_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3);
v___x_701_ = lean_string_append(v___x_700_, v___x_699_);
return v___x_701_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = 1;
v___x_705_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__5));
v___x_706_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_705_, v___x_704_);
return v___x_706_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_707_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6);
v___x_708_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4);
v___x_709_ = lean_string_append(v___x_708_, v___x_707_);
return v___x_709_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_710_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10));
v___x_711_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7);
v___x_712_ = lean_string_append(v___x_711_, v___x_710_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson(lean_object* v_json_713_){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0));
v___x_715_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0(v_json_713_, v___x_714_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_725_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_725_ == 0)
{
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_725_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_725_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_720_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8);
v___x_721_ = lean_string_append(v___x_720_, v_a_716_);
lean_dec(v_a_716_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_721_);
v___x_723_ = v___x_718_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
v_a_726_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_715_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_715_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0(size_t v_sz_736_, size_t v_i_737_, lean_object* v_bs_738_){
_start:
{
uint8_t v___x_739_; 
v___x_739_ = lean_usize_dec_lt(v_i_737_, v_sz_736_);
if (v___x_739_ == 0)
{
return v_bs_738_;
}
else
{
lean_object* v_v_740_; lean_object* v___x_741_; lean_object* v_bs_x27_742_; lean_object* v___x_743_; size_t v___x_744_; size_t v___x_745_; lean_object* v___x_746_; 
v_v_740_ = lean_array_uget(v_bs_738_, v_i_737_);
v___x_741_ = lean_unsigned_to_nat(0u);
v_bs_x27_742_ = lean_array_uset(v_bs_738_, v_i_737_, v___x_741_);
v___x_743_ = l_Lean_Lsp_instToJsonFileEvent_toJson(v_v_740_);
lean_dec(v_v_740_);
v___x_744_ = ((size_t)1ULL);
v___x_745_ = lean_usize_add(v_i_737_, v___x_744_);
v___x_746_ = lean_array_uset(v_bs_x27_742_, v_i_737_, v___x_743_);
v_i_737_ = v___x_745_;
v_bs_738_ = v___x_746_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_748_, lean_object* v_i_749_, lean_object* v_bs_750_){
_start:
{
size_t v_sz_boxed_751_; size_t v_i_boxed_752_; lean_object* v_res_753_; 
v_sz_boxed_751_ = lean_unbox_usize(v_sz_748_);
lean_dec(v_sz_748_);
v_i_boxed_752_ = lean_unbox_usize(v_i_749_);
lean_dec(v_i_749_);
v_res_753_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0(v_sz_boxed_751_, v_i_boxed_752_, v_bs_750_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0(lean_object* v_a_754_){
_start:
{
size_t v_sz_755_; size_t v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_sz_755_ = lean_array_size(v_a_754_);
v___x_756_ = ((size_t)0ULL);
v___x_757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0(v_sz_755_, v___x_756_, v_a_754_);
v___x_758_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson(lean_object* v_x_759_){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_760_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0));
v___x_761_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0(v_x_759_);
v___x_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_760_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = lean_box(0);
v___x_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_762_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v___x_763_);
v___x_766_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2));
v___x_767_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(v___x_765_, v___x_766_);
v___x_768_ = l_Lean_Json_mkObj(v___x_767_);
lean_dec(v___x_767_);
return v___x_768_;
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
