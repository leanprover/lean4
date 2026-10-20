// Lean compiler output
// Module: Lean.Setup
// Imports: public import Lean.Data.Json.Parser public import Lean.Util.LeanOptions
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* lean_string_length(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_instReprLeanOptions_repr___redArg(lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_instFromJsonFilePath___lam__0(lean_object*);
lean_object* l_Lean_Array_fromJson_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Array_fromJson_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instToJsonFilePath___lam__0(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Array_toJson(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Array_toJson___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprImport_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_instReprImport_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_instReprImport_repr___redArg___closed__0 = (const lean_object*)&l_Lean_instReprImport_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_instReprImport_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lean_instReprImport_repr___redArg___closed__1 = (const lean_object*)&l_Lean_instReprImport_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instReprImport_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprImport_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_instReprImport_repr___redArg___closed__2 = (const lean_object*)&l_Lean_instReprImport_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_instReprImport_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprImport_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_instReprImport_repr___redArg___closed__3 = (const lean_object*)&l_Lean_instReprImport_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_instReprImport_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_instReprImport_repr___redArg___closed__4 = (const lean_object*)&l_Lean_instReprImport_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_instReprImport_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprImport_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_instReprImport_repr___redArg___closed__5 = (const lean_object*)&l_Lean_instReprImport_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_instReprImport_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprImport_repr___redArg___closed__3_value),((lean_object*)&l_Lean_instReprImport_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprImport_repr___redArg___closed__6 = (const lean_object*)&l_Lean_instReprImport_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_instReprImport_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprImport_repr___redArg___closed__7;
static const lean_string_object l_Lean_instReprImport_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_instReprImport_repr___redArg___closed__8 = (const lean_object*)&l_Lean_instReprImport_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_instReprImport_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprImport_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_instReprImport_repr___redArg___closed__9 = (const lean_object*)&l_Lean_instReprImport_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_instReprImport_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "importAll"};
static const lean_object* l_Lean_instReprImport_repr___redArg___closed__10 = (const lean_object*)&l_Lean_instReprImport_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_instReprImport_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprImport_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_instReprImport_repr___redArg___closed__11 = (const lean_object*)&l_Lean_instReprImport_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_instReprImport_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprImport_repr___redArg___closed__12;
static const lean_string_object l_Lean_instReprImport_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "isExported"};
static const lean_object* l_Lean_instReprImport_repr___redArg___closed__13 = (const lean_object*)&l_Lean_instReprImport_repr___redArg___closed__13_value;
static const lean_ctor_object l_Lean_instReprImport_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprImport_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_instReprImport_repr___redArg___closed__14 = (const lean_object*)&l_Lean_instReprImport_repr___redArg___closed__14_value;
static lean_once_cell_t l_Lean_instReprImport_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprImport_repr___redArg___closed__15;
static const lean_string_object l_Lean_instReprImport_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isMeta"};
static const lean_object* l_Lean_instReprImport_repr___redArg___closed__16 = (const lean_object*)&l_Lean_instReprImport_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lean_instReprImport_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprImport_repr___redArg___closed__16_value)}};
static const lean_object* l_Lean_instReprImport_repr___redArg___closed__17 = (const lean_object*)&l_Lean_instReprImport_repr___redArg___closed__17_value;
static const lean_string_object l_Lean_instReprImport_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_instReprImport_repr___redArg___closed__18 = (const lean_object*)&l_Lean_instReprImport_repr___redArg___closed__18_value;
static lean_once_cell_t l_Lean_instReprImport_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprImport_repr___redArg___closed__19;
static lean_once_cell_t l_Lean_instReprImport_repr___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprImport_repr___redArg___closed__20;
static const lean_ctor_object l_Lean_instReprImport_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprImport_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_instReprImport_repr___redArg___closed__21 = (const lean_object*)&l_Lean_instReprImport_repr___redArg___closed__21_value;
static const lean_ctor_object l_Lean_instReprImport_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprImport_repr___redArg___closed__18_value)}};
static const lean_object* l_Lean_instReprImport_repr___redArg___closed__22 = (const lean_object*)&l_Lean_instReprImport_repr___redArg___closed__22_value;
LEAN_EXPORT lean_object* l_Lean_instReprImport_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprImport_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprImport_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprImport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprImport_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprImport___closed__0 = (const lean_object*)&l_Lean_instReprImport___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprImport = (const lean_object*)&l_Lean_instReprImport___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedImport_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_instInhabitedImport_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedImport_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedImport_default = (const lean_object*)&l_Lean_instInhabitedImport_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedImport = (const lean_object*)&l_Lean_instInhabitedImport_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(lean_object*, lean_object*);
static const lean_array_object l_Lean_instToJsonImport_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instToJsonImport_toJson___closed__0 = (const lean_object*)&l_Lean_instToJsonImport_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonImport_toJson(lean_object*);
static const lean_closure_object l_Lean_instToJsonImport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonImport_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonImport___closed__0 = (const lean_object*)&l_Lean_instToJsonImport___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonImport = (const lean_object*)&l_Lean_instToJsonImport___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_instFromJsonImport_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_instFromJsonImport_fromJson___closed__0 = (const lean_object*)&l_Lean_instFromJsonImport_fromJson___closed__0_value;
static const lean_string_object l_Lean_instFromJsonImport_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Import"};
static const lean_object* l_Lean_instFromJsonImport_fromJson___closed__1 = (const lean_object*)&l_Lean_instFromJsonImport_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_instFromJsonImport_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instFromJsonImport_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instFromJsonImport_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instFromJsonImport_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_instFromJsonImport_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(29, 47, 116, 218, 39, 28, 172, 37)}};
static const lean_object* l_Lean_instFromJsonImport_fromJson___closed__2 = (const lean_object*)&l_Lean_instFromJsonImport_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_instFromJsonImport_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonImport_fromJson___closed__3;
static const lean_string_object l_Lean_instFromJsonImport_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_instFromJsonImport_fromJson___closed__4 = (const lean_object*)&l_Lean_instFromJsonImport_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_instFromJsonImport_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonImport_fromJson___closed__5;
static const lean_ctor_object l_Lean_instFromJsonImport_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprImport_repr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_object* l_Lean_instFromJsonImport_fromJson___closed__6 = (const lean_object*)&l_Lean_instFromJsonImport_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_instFromJsonImport_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonImport_fromJson___closed__7;
static lean_once_cell_t l_Lean_instFromJsonImport_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonImport_fromJson___closed__8;
static const lean_string_object l_Lean_instFromJsonImport_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_instFromJsonImport_fromJson___closed__9 = (const lean_object*)&l_Lean_instFromJsonImport_fromJson___closed__9_value;
static lean_once_cell_t l_Lean_instFromJsonImport_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonImport_fromJson___closed__10;
static const lean_ctor_object l_Lean_instFromJsonImport_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprImport_repr___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(55, 207, 23, 186, 33, 19, 88, 171)}};
static const lean_object* l_Lean_instFromJsonImport_fromJson___closed__11 = (const lean_object*)&l_Lean_instFromJsonImport_fromJson___closed__11_value;
static lean_once_cell_t l_Lean_instFromJsonImport_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonImport_fromJson___closed__12;
static lean_once_cell_t l_Lean_instFromJsonImport_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonImport_fromJson___closed__13;
static lean_once_cell_t l_Lean_instFromJsonImport_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonImport_fromJson___closed__14;
static const lean_ctor_object l_Lean_instFromJsonImport_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprImport_repr___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(18, 58, 236, 181, 205, 109, 15, 233)}};
static const lean_object* l_Lean_instFromJsonImport_fromJson___closed__15 = (const lean_object*)&l_Lean_instFromJsonImport_fromJson___closed__15_value;
static lean_once_cell_t l_Lean_instFromJsonImport_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonImport_fromJson___closed__16;
static lean_once_cell_t l_Lean_instFromJsonImport_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonImport_fromJson___closed__17;
static lean_once_cell_t l_Lean_instFromJsonImport_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonImport_fromJson___closed__18;
static const lean_ctor_object l_Lean_instFromJsonImport_fromJson___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprImport_repr___redArg___closed__16_value),LEAN_SCALAR_PTR_LITERAL(249, 28, 190, 209, 3, 53, 190, 55)}};
static const lean_object* l_Lean_instFromJsonImport_fromJson___closed__19 = (const lean_object*)&l_Lean_instFromJsonImport_fromJson___closed__19_value;
static lean_once_cell_t l_Lean_instFromJsonImport_fromJson___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonImport_fromJson___closed__20;
static lean_once_cell_t l_Lean_instFromJsonImport_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonImport_fromJson___closed__21;
static lean_once_cell_t l_Lean_instFromJsonImport_fromJson___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonImport_fromJson___closed__22;
LEAN_EXPORT lean_object* l_Lean_instFromJsonImport_fromJson(lean_object*);
static const lean_closure_object l_Lean_instFromJsonImport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonImport_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonImport___closed__0 = (const lean_object*)&l_Lean_instFromJsonImport___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonImport = (const lean_object*)&l_Lean_instFromJsonImport___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_instBEqImport_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqImport_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqImport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqImport_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqImport___closed__0 = (const lean_object*)&l_Lean_instBEqImport___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqImport = (const lean_object*)&l_Lean_instBEqImport___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_instHashableImport_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableImport_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableImport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableImport_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableImport___closed__0 = (const lean_object*)&l_Lean_instHashableImport___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableImport = (const lean_object*)&l_Lean_instHashableImport___closed__0_value;
lean_object* lean_idbg_client_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Idbg_idbgClientLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instCoeNameImport___lam__0(lean_object*);
static const lean_closure_object l_Lean_instCoeNameImport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instCoeNameImport___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instCoeNameImport___closed__0 = (const lean_object*)&l_Lean_instCoeNameImport___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instCoeNameImport = (const lean_object*)&l_Lean_instCoeNameImport___closed__0_value;
static const lean_string_object l_Lean_instToStringImport___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "import "};
static const lean_object* l_Lean_instToStringImport___lam__0___closed__0 = (const lean_object*)&l_Lean_instToStringImport___lam__0___closed__0_value;
static const lean_string_object l_Lean_instToStringImport___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_instToStringImport___lam__0___closed__1 = (const lean_object*)&l_Lean_instToStringImport___lam__0___closed__1_value;
static const lean_string_object l_Lean_instToStringImport___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "all "};
static const lean_object* l_Lean_instToStringImport___lam__0___closed__2 = (const lean_object*)&l_Lean_instToStringImport___lam__0___closed__2_value;
static const lean_string_object l_Lean_instToStringImport___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "meta "};
static const lean_object* l_Lean_instToStringImport___lam__0___closed__3 = (const lean_object*)&l_Lean_instToStringImport___lam__0___closed__3_value;
static const lean_string_object l_Lean_instToStringImport___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "public "};
static const lean_object* l_Lean_instToStringImport___lam__0___closed__4 = (const lean_object*)&l_Lean_instToStringImport___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_instToStringImport___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToStringImport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToStringImport___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToStringImport___closed__0 = (const lean_object*)&l_Lean_instToStringImport___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToStringImport = (const lean_object*)&l_Lean_instToStringImport___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IRPhases_runtime_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IRPhases_runtime_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IRPhases_runtime_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IRPhases_runtime_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IRPhases_comptime_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IRPhases_comptime_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IRPhases_comptime_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IRPhases_comptime_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IRPhases_all_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IRPhases_all_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IRPhases_all_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IRPhases_all_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedIRPhases_default;
LEAN_EXPORT uint8_t l_Lean_instInhabitedIRPhases;
LEAN_EXPORT uint8_t l_Lean_instBEqIRPhases_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instBEqIRPhases_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqIRPhases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqIRPhases_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqIRPhases___closed__0 = (const lean_object*)&l_Lean_instBEqIRPhases___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqIRPhases = (const lean_object*)&l_Lean_instBEqIRPhases___closed__0_value;
static const lean_string_object l_Lean_instReprIRPhases_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.IRPhases.runtime"};
static const lean_object* l_Lean_instReprIRPhases_repr___closed__0 = (const lean_object*)&l_Lean_instReprIRPhases_repr___closed__0_value;
static const lean_ctor_object l_Lean_instReprIRPhases_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprIRPhases_repr___closed__0_value)}};
static const lean_object* l_Lean_instReprIRPhases_repr___closed__1 = (const lean_object*)&l_Lean_instReprIRPhases_repr___closed__1_value;
static const lean_string_object l_Lean_instReprIRPhases_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.IRPhases.comptime"};
static const lean_object* l_Lean_instReprIRPhases_repr___closed__2 = (const lean_object*)&l_Lean_instReprIRPhases_repr___closed__2_value;
static const lean_ctor_object l_Lean_instReprIRPhases_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprIRPhases_repr___closed__2_value)}};
static const lean_object* l_Lean_instReprIRPhases_repr___closed__3 = (const lean_object*)&l_Lean_instReprIRPhases_repr___closed__3_value;
static const lean_string_object l_Lean_instReprIRPhases_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.IRPhases.all"};
static const lean_object* l_Lean_instReprIRPhases_repr___closed__4 = (const lean_object*)&l_Lean_instReprIRPhases_repr___closed__4_value;
static const lean_ctor_object l_Lean_instReprIRPhases_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprIRPhases_repr___closed__4_value)}};
static const lean_object* l_Lean_instReprIRPhases_repr___closed__5 = (const lean_object*)&l_Lean_instReprIRPhases_repr___closed__5_value;
static lean_once_cell_t l_Lean_instReprIRPhases_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprIRPhases_repr___closed__6;
static lean_once_cell_t l_Lean_instReprIRPhases_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprIRPhases_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_instReprIRPhases_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprIRPhases_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprIRPhases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprIRPhases_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprIRPhases___closed__0 = (const lean_object*)&l_Lean_instReprIRPhases___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprIRPhases = (const lean_object*)&l_Lean_instReprIRPhases___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprImport_repr___redArg___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1_value;
static const lean_string_object l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__2_value;
static lean_once_cell_t l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3;
static lean_once_cell_t l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4;
static const lean_ctor_object l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5 = (const lean_object*)&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5_value;
static const lean_ctor_object l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__2_value)}};
static const lean_object* l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6 = (const lean_object*)&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6_value;
static const lean_string_object l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__7_value)}};
static const lean_object* l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_instReprModuleHeader_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "imports"};
static const lean_object* l_Lean_instReprModuleHeader_repr___redArg___closed__0 = (const lean_object*)&l_Lean_instReprModuleHeader_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_instReprModuleHeader_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprModuleHeader_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_instReprModuleHeader_repr___redArg___closed__1 = (const lean_object*)&l_Lean_instReprModuleHeader_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instReprModuleHeader_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleHeader_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_instReprModuleHeader_repr___redArg___closed__2 = (const lean_object*)&l_Lean_instReprModuleHeader_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_instReprModuleHeader_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprModuleHeader_repr___redArg___closed__2_value),((lean_object*)&l_Lean_instReprImport_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprModuleHeader_repr___redArg___closed__3 = (const lean_object*)&l_Lean_instReprModuleHeader_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_instReprModuleHeader_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprModuleHeader_repr___redArg___closed__4;
static const lean_string_object l_Lean_instReprModuleHeader_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "isModule"};
static const lean_object* l_Lean_instReprModuleHeader_repr___redArg___closed__5 = (const lean_object*)&l_Lean_instReprModuleHeader_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_instReprModuleHeader_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprModuleHeader_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprModuleHeader_repr___redArg___closed__6 = (const lean_object*)&l_Lean_instReprModuleHeader_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_instReprModuleHeader_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprModuleHeader_repr___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_instReprModuleHeader_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprModuleHeader_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprModuleHeader_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprModuleHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprModuleHeader_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprModuleHeader___closed__0 = (const lean_object*)&l_Lean_instReprModuleHeader___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprModuleHeader = (const lean_object*)&l_Lean_instReprModuleHeader___closed__0_value;
static const lean_array_object l_Lean_instInhabitedModuleHeader_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedModuleHeader_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedModuleHeader_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedModuleHeader_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedModuleHeader_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_instInhabitedModuleHeader_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedModuleHeader_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedModuleHeader_default = (const lean_object*)&l_Lean_instInhabitedModuleHeader_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedModuleHeader = (const lean_object*)&l_Lean_instInhabitedModuleHeader_default___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonModuleHeader_toJson(lean_object*);
static const lean_closure_object l_Lean_instToJsonModuleHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonModuleHeader_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonModuleHeader___closed__0 = (const lean_object*)&l_Lean_instToJsonModuleHeader___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonModuleHeader = (const lean_object*)&l_Lean_instToJsonModuleHeader___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_instFromJsonModuleHeader_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ModuleHeader"};
static const lean_object* l_Lean_instFromJsonModuleHeader_fromJson___closed__0 = (const lean_object*)&l_Lean_instFromJsonModuleHeader_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_instFromJsonModuleHeader_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instFromJsonImport_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instFromJsonModuleHeader_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instFromJsonModuleHeader_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_instFromJsonModuleHeader_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 133, 47, 53, 204, 105, 198, 136)}};
static const lean_object* l_Lean_instFromJsonModuleHeader_fromJson___closed__1 = (const lean_object*)&l_Lean_instFromJsonModuleHeader_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_instFromJsonModuleHeader_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleHeader_fromJson___closed__2;
static lean_once_cell_t l_Lean_instFromJsonModuleHeader_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleHeader_fromJson___closed__3;
static const lean_ctor_object l_Lean_instFromJsonModuleHeader_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleHeader_repr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 36, 215, 236, 248, 74, 62, 169)}};
static const lean_object* l_Lean_instFromJsonModuleHeader_fromJson___closed__4 = (const lean_object*)&l_Lean_instFromJsonModuleHeader_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_instFromJsonModuleHeader_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleHeader_fromJson___closed__5;
static lean_once_cell_t l_Lean_instFromJsonModuleHeader_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleHeader_fromJson___closed__6;
static lean_once_cell_t l_Lean_instFromJsonModuleHeader_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleHeader_fromJson___closed__7;
static const lean_ctor_object l_Lean_instFromJsonModuleHeader_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleHeader_repr___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(63, 113, 75, 226, 154, 4, 86, 101)}};
static const lean_object* l_Lean_instFromJsonModuleHeader_fromJson___closed__8 = (const lean_object*)&l_Lean_instFromJsonModuleHeader_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_instFromJsonModuleHeader_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleHeader_fromJson___closed__9;
static lean_once_cell_t l_Lean_instFromJsonModuleHeader_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleHeader_fromJson___closed__10;
static lean_once_cell_t l_Lean_instFromJsonModuleHeader_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleHeader_fromJson___closed__11;
LEAN_EXPORT lean_object* l_Lean_instFromJsonModuleHeader_fromJson(lean_object*);
static const lean_closure_object l_Lean_instFromJsonModuleHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonModuleHeader_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonModuleHeader___closed__0 = (const lean_object*)&l_Lean_instFromJsonModuleHeader___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonModuleHeader = (const lean_object*)&l_Lean_instFromJsonModuleHeader___closed__0_value;
static const lean_string_object l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "FilePath.mk "};
static const lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0___closed__0 = (const lean_object*)&l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0___closed__0_value)}};
static const lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0___closed__1 = (const lean_object*)&l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_instReprImportArtifacts_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toArrays"};
static const lean_object* l_Lean_instReprImportArtifacts_repr___redArg___closed__0 = (const lean_object*)&l_Lean_instReprImportArtifacts_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_instReprImportArtifacts_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprImportArtifacts_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_instReprImportArtifacts_repr___redArg___closed__1 = (const lean_object*)&l_Lean_instReprImportArtifacts_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instReprImportArtifacts_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprImportArtifacts_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_instReprImportArtifacts_repr___redArg___closed__2 = (const lean_object*)&l_Lean_instReprImportArtifacts_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_instReprImportArtifacts_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprImportArtifacts_repr___redArg___closed__2_value),((lean_object*)&l_Lean_instReprImport_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprImportArtifacts_repr___redArg___closed__3 = (const lean_object*)&l_Lean_instReprImportArtifacts_repr___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_instReprImportArtifacts_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprImportArtifacts_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprImportArtifacts_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprImportArtifacts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprImportArtifacts_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprImportArtifacts___closed__0 = (const lean_object*)&l_Lean_instReprImportArtifacts___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprImportArtifacts = (const lean_object*)&l_Lean_instReprImportArtifacts___closed__0_value;
static const lean_array_object l_Lean_instInhabitedImportArtifacts_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedImportArtifacts_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedImportArtifacts_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedImportArtifacts_default = (const lean_object*)&l_Lean_instInhabitedImportArtifacts_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedImportArtifacts = (const lean_object*)&l_Lean_instInhabitedImportArtifacts_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonImportArtifacts___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instToJsonImportArtifacts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonFilePath___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonImportArtifacts___closed__0 = (const lean_object*)&l_Lean_instToJsonImportArtifacts___closed__0_value;
static const lean_closure_object l_Lean_instToJsonImportArtifacts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Array_toJson, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToJsonImportArtifacts___closed__0_value)} };
static const lean_object* l_Lean_instToJsonImportArtifacts___closed__1 = (const lean_object*)&l_Lean_instToJsonImportArtifacts___closed__1_value;
static const lean_closure_object l_Lean_instToJsonImportArtifacts___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonImportArtifacts___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_instToJsonImportArtifacts___closed__1_value)} };
static const lean_object* l_Lean_instToJsonImportArtifacts___closed__2 = (const lean_object*)&l_Lean_instToJsonImportArtifacts___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonImportArtifacts = (const lean_object*)&l_Lean_instToJsonImportArtifacts___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_instFromJsonImportArtifacts___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instFromJsonImportArtifacts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonFilePath___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonImportArtifacts___closed__0 = (const lean_object*)&l_Lean_instFromJsonImportArtifacts___closed__0_value;
static const lean_closure_object l_Lean_instFromJsonImportArtifacts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Array_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instFromJsonImportArtifacts___closed__0_value)} };
static const lean_object* l_Lean_instFromJsonImportArtifacts___closed__1 = (const lean_object*)&l_Lean_instFromJsonImportArtifacts___closed__1_value;
static const lean_closure_object l_Lean_instFromJsonImportArtifacts___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonImportArtifacts___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_instFromJsonImportArtifacts___closed__1_value)} };
static const lean_object* l_Lean_instFromJsonImportArtifacts___closed__2 = (const lean_object*)&l_Lean_instFromJsonImportArtifacts___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonImportArtifacts = (const lean_object*)&l_Lean_instFromJsonImportArtifacts___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_olean_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_olean_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanServer_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanServer_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanPrivate_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanPrivate_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_irSig_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_irSig_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_ir_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_ir_x3f___boxed(lean_object*);
static const lean_array_object l_Lean_ImportArtifacts_oleanParts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_ImportArtifacts_oleanParts___closed__0 = (const lean_object*)&l_Lean_ImportArtifacts_oleanParts___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanParts(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanParts___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_irParts(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_irParts___boxed(lean_object*);
static const lean_string_object l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__1_value;
static const lean_string_object l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__3 = (const lean_object*)&l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "lean\?"};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__0 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__1 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__2 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__2_value),((lean_object*)&l_Lean_instReprImport_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__3 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_instReprModuleArtifacts_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__4;
static const lean_string_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "olean\?"};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__5 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__6 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__6_value;
static const lean_string_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "oleanServer\?"};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__7 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__7_value)}};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__8 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__8_value;
static lean_once_cell_t l_Lean_instReprModuleArtifacts_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__9;
static const lean_string_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "oleanPrivate\?"};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__10 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__11 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_instReprModuleArtifacts_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__12;
static const lean_string_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ilean\?"};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__13 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__13_value;
static const lean_ctor_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__14 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__14_value;
static const lean_string_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "irSig\?"};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__15 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__15_value;
static const lean_ctor_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__15_value)}};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__16 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__16_value;
static const lean_string_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ir\?"};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__17 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__17_value;
static const lean_ctor_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__17_value)}};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__18 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__18_value;
static lean_once_cell_t l_Lean_instReprModuleArtifacts_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__19;
static const lean_string_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "c\?"};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__20 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__20_value;
static const lean_ctor_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__20_value)}};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__21 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__21_value;
static lean_once_cell_t l_Lean_instReprModuleArtifacts_repr___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__22;
static const lean_string_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bc\?"};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__23 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__23_value;
static const lean_ctor_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__23_value)}};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__24 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__24_value;
LEAN_EXPORT lean_object* l_Lean_instReprModuleArtifacts_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprModuleArtifacts_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprModuleArtifacts_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprModuleArtifacts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprModuleArtifacts_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprModuleArtifacts___closed__0 = (const lean_object*)&l_Lean_instReprModuleArtifacts___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprModuleArtifacts = (const lean_object*)&l_Lean_instReprModuleArtifacts___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedModuleArtifacts_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*9 + 0, .m_other = 9, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_instInhabitedModuleArtifacts_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedModuleArtifacts_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedModuleArtifacts_default = (const lean_object*)&l_Lean_instInhabitedModuleArtifacts_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedModuleArtifacts = (const lean_object*)&l_Lean_instInhabitedModuleArtifacts_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_instToJsonModuleArtifacts_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_instToJsonModuleArtifacts_toJson___closed__0 = (const lean_object*)&l_Lean_instToJsonModuleArtifacts_toJson___closed__0_value;
static const lean_string_object l_Lean_instToJsonModuleArtifacts_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "olean"};
static const lean_object* l_Lean_instToJsonModuleArtifacts_toJson___closed__1 = (const lean_object*)&l_Lean_instToJsonModuleArtifacts_toJson___closed__1_value;
static const lean_string_object l_Lean_instToJsonModuleArtifacts_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "oleanServer"};
static const lean_object* l_Lean_instToJsonModuleArtifacts_toJson___closed__2 = (const lean_object*)&l_Lean_instToJsonModuleArtifacts_toJson___closed__2_value;
static const lean_string_object l_Lean_instToJsonModuleArtifacts_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "oleanPrivate"};
static const lean_object* l_Lean_instToJsonModuleArtifacts_toJson___closed__3 = (const lean_object*)&l_Lean_instToJsonModuleArtifacts_toJson___closed__3_value;
static const lean_string_object l_Lean_instToJsonModuleArtifacts_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ilean"};
static const lean_object* l_Lean_instToJsonModuleArtifacts_toJson___closed__4 = (const lean_object*)&l_Lean_instToJsonModuleArtifacts_toJson___closed__4_value;
static const lean_string_object l_Lean_instToJsonModuleArtifacts_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "irSig"};
static const lean_object* l_Lean_instToJsonModuleArtifacts_toJson___closed__5 = (const lean_object*)&l_Lean_instToJsonModuleArtifacts_toJson___closed__5_value;
static const lean_string_object l_Lean_instToJsonModuleArtifacts_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l_Lean_instToJsonModuleArtifacts_toJson___closed__6 = (const lean_object*)&l_Lean_instToJsonModuleArtifacts_toJson___closed__6_value;
static const lean_string_object l_Lean_instToJsonModuleArtifacts_toJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "c"};
static const lean_object* l_Lean_instToJsonModuleArtifacts_toJson___closed__7 = (const lean_object*)&l_Lean_instToJsonModuleArtifacts_toJson___closed__7_value;
static const lean_string_object l_Lean_instToJsonModuleArtifacts_toJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bc"};
static const lean_object* l_Lean_instToJsonModuleArtifacts_toJson___closed__8 = (const lean_object*)&l_Lean_instToJsonModuleArtifacts_toJson___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonModuleArtifacts_toJson(lean_object*);
static const lean_closure_object l_Lean_instToJsonModuleArtifacts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonModuleArtifacts_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonModuleArtifacts___closed__0 = (const lean_object*)&l_Lean_instToJsonModuleArtifacts___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonModuleArtifacts = (const lean_object*)&l_Lean_instToJsonModuleArtifacts___closed__0_value;
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_instFromJsonModuleArtifacts_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "ModuleArtifacts"};
static const lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__0 = (const lean_object*)&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_instFromJsonModuleArtifacts_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instFromJsonImport_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instFromJsonModuleArtifacts_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 81, 219, 106, 80, 78, 212, 83)}};
static const lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__1 = (const lean_object*)&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3;
static const lean_ctor_object l_Lean_instFromJsonModuleArtifacts_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 97, 121, 84, 79, 57, 27, 198)}};
static const lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__4 = (const lean_object*)&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7;
static const lean_ctor_object l_Lean_instFromJsonModuleArtifacts_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(92, 73, 25, 68, 136, 230, 12, 70)}};
static const lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__8 = (const lean_object*)&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11;
static const lean_ctor_object l_Lean_instFromJsonModuleArtifacts_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(73, 89, 207, 118, 14, 195, 79, 46)}};
static const lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__12 = (const lean_object*)&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__12_value;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15;
static const lean_ctor_object l_Lean_instFromJsonModuleArtifacts_fromJson___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(208, 81, 131, 149, 87, 174, 61, 121)}};
static const lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__16 = (const lean_object*)&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__16_value;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19;
static const lean_ctor_object l_Lean_instFromJsonModuleArtifacts_fromJson___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(71, 198, 131, 151, 180, 121, 147, 129)}};
static const lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__20 = (const lean_object*)&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__20_value;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23;
static const lean_ctor_object l_Lean_instFromJsonModuleArtifacts_fromJson___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(115, 165, 122, 11, 39, 10, 7, 18)}};
static const lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__24 = (const lean_object*)&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__24_value;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27;
static const lean_ctor_object l_Lean_instFromJsonModuleArtifacts_fromJson___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__17_value),LEAN_SCALAR_PTR_LITERAL(107, 198, 234, 26, 172, 111, 119, 17)}};
static const lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__28 = (const lean_object*)&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__28_value;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31;
static const lean_ctor_object l_Lean_instFromJsonModuleArtifacts_fromJson___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(31, 145, 40, 88, 138, 45, 124, 142)}};
static const lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__32 = (const lean_object*)&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__32_value;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35;
static const lean_ctor_object l_Lean_instFromJsonModuleArtifacts_fromJson___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(38, 234, 246, 30, 222, 18, 116, 36)}};
static const lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__36 = (const lean_object*)&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__36_value;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__37;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__38;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__39;
LEAN_EXPORT lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson(lean_object*);
static const lean_closure_object l_Lean_instFromJsonModuleArtifacts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonModuleArtifacts_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonModuleArtifacts___closed__0 = (const lean_object*)&l_Lean_instFromJsonModuleArtifacts___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonModuleArtifacts = (const lean_object*)&l_Lean_instFromJsonModuleArtifacts___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_ModuleArtifacts_oleanParts(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleArtifacts_irParts(lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_instReprPlugin_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "path"};
static const lean_object* l_Lean_instReprPlugin_repr___redArg___closed__0 = (const lean_object*)&l_Lean_instReprPlugin_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_instReprPlugin_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprPlugin_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_instReprPlugin_repr___redArg___closed__1 = (const lean_object*)&l_Lean_instReprPlugin_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instReprPlugin_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprPlugin_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_instReprPlugin_repr___redArg___closed__2 = (const lean_object*)&l_Lean_instReprPlugin_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_instReprPlugin_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprPlugin_repr___redArg___closed__2_value),((lean_object*)&l_Lean_instReprImport_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprPlugin_repr___redArg___closed__3 = (const lean_object*)&l_Lean_instReprPlugin_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_instReprPlugin_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprPlugin_repr___redArg___closed__4;
static const lean_string_object l_Lean_instReprPlugin_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "initFn\?"};
static const lean_object* l_Lean_instReprPlugin_repr___redArg___closed__5 = (const lean_object*)&l_Lean_instReprPlugin_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_instReprPlugin_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprPlugin_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprPlugin_repr___redArg___closed__6 = (const lean_object*)&l_Lean_instReprPlugin_repr___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_instReprPlugin_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprPlugin_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprPlugin_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprPlugin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprPlugin_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprPlugin___closed__0 = (const lean_object*)&l_Lean_instReprPlugin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprPlugin = (const lean_object*)&l_Lean_instReprPlugin___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonPlugin_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_instToJsonPlugin_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l_Lean_instToJsonPlugin_toJson___closed__0 = (const lean_object*)&l_Lean_instToJsonPlugin_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonPlugin_toJson(lean_object*);
static const lean_closure_object l_Lean_instToJsonPlugin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonPlugin_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonPlugin___closed__0 = (const lean_object*)&l_Lean_instToJsonPlugin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonPlugin = (const lean_object*)&l_Lean_instToJsonPlugin___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Plugin_ofFilePath(lean_object*);
static const lean_closure_object l_Lean_Plugin_instCoeFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Plugin_ofFilePath, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Plugin_instCoeFilePath___closed__0 = (const lean_object*)&l_Lean_Plugin_instCoeFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Plugin_instCoeFilePath = (const lean_object*)&l_Lean_Plugin_instCoeFilePath___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Plugin_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "expected string or object"};
static const lean_object* l_Lean_Plugin_fromJson_x3f___closed__0 = (const lean_object*)&l_Lean_Plugin_fromJson_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Plugin_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Plugin_fromJson_x3f___closed__0_value)}};
static const lean_object* l_Lean_Plugin_fromJson_x3f___closed__1 = (const lean_object*)&l_Lean_Plugin_fromJson_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Plugin_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lean_Plugin_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Plugin_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Plugin_instFromJson___closed__0 = (const lean_object*)&l_Lean_Plugin_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Plugin_instFromJson = (const lean_object*)&l_Lean_Plugin_instFromJson___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2_spec__3(lean_object*, lean_object*);
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__0_value;
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__4 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__4_value;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__5 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3(lean_object*, lean_object*);
static const lean_string_object l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__0_value)}};
static const lean_object* l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__1 = (const lean_object*)&l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__1_value;
static const lean_string_object l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__2 = (const lean_object*)&l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3;
static lean_once_cell_t l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4;
static const lean_ctor_object l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__2_value)}};
static const lean_object* l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__5 = (const lean_object*)&l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5_spec__8_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprModuleSetup_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprModuleSetup_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_instReprModuleSetup_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_instReprModuleSetup_repr___redArg___closed__0 = (const lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_instReprModuleSetup_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_instReprModuleSetup_repr___redArg___closed__1 = (const lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instReprModuleSetup_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_instReprModuleSetup_repr___redArg___closed__2 = (const lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_instReprModuleSetup_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__2_value),((lean_object*)&l_Lean_instReprImport_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprModuleSetup_repr___redArg___closed__3 = (const lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_instReprModuleSetup_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "package\?"};
static const lean_object* l_Lean_instReprModuleSetup_repr___redArg___closed__4 = (const lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_instReprModuleSetup_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_instReprModuleSetup_repr___redArg___closed__5 = (const lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__5_value;
static const lean_string_object l_Lean_instReprModuleSetup_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "imports\?"};
static const lean_object* l_Lean_instReprModuleSetup_repr___redArg___closed__6 = (const lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__6_value;
static const lean_ctor_object l_Lean_instReprModuleSetup_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__6_value)}};
static const lean_object* l_Lean_instReprModuleSetup_repr___redArg___closed__7 = (const lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__7_value;
static const lean_string_object l_Lean_instReprModuleSetup_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "importArts"};
static const lean_object* l_Lean_instReprModuleSetup_repr___redArg___closed__8 = (const lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_instReprModuleSetup_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_instReprModuleSetup_repr___redArg___closed__9 = (const lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_instReprModuleSetup_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.TreeMap.ofList "};
static const lean_object* l_Lean_instReprModuleSetup_repr___redArg___closed__10 = (const lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_instReprModuleSetup_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_instReprModuleSetup_repr___redArg___closed__11 = (const lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__11_value;
static const lean_string_object l_Lean_instReprModuleSetup_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "dynlibs"};
static const lean_object* l_Lean_instReprModuleSetup_repr___redArg___closed__12 = (const lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lean_instReprModuleSetup_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__12_value)}};
static const lean_object* l_Lean_instReprModuleSetup_repr___redArg___closed__13 = (const lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__13_value;
static const lean_string_object l_Lean_instReprModuleSetup_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "plugins"};
static const lean_object* l_Lean_instReprModuleSetup_repr___redArg___closed__14 = (const lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_instReprModuleSetup_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_instReprModuleSetup_repr___redArg___closed__15 = (const lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__15_value;
static const lean_string_object l_Lean_instReprModuleSetup_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "options"};
static const lean_object* l_Lean_instReprModuleSetup_repr___redArg___closed__16 = (const lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lean_instReprModuleSetup_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__16_value)}};
static const lean_object* l_Lean_instReprModuleSetup_repr___redArg___closed__17 = (const lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__17_value;
LEAN_EXPORT lean_object* l_Lean_instReprModuleSetup_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprModuleSetup_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprModuleSetup_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprModuleSetup___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprModuleSetup_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprModuleSetup___closed__0 = (const lean_object*)&l_Lean_instReprModuleSetup___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprModuleSetup = (const lean_object*)&l_Lean_instReprModuleSetup___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedModuleSetup_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_ImportArtifacts_oleanParts___closed__0_value),((lean_object*)&l_Lean_ImportArtifacts_oleanParts___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_instInhabitedModuleSetup_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedModuleSetup_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedModuleSetup_default = (const lean_object*)&l_Lean_instInhabitedModuleSetup_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedModuleSetup = (const lean_object*)&l_Lean_instInhabitedModuleSetup_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4___redArg(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Data.DTreeMap.Internal.Balancing"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__6_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__7;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__8;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonModuleSetup_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__9_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3(lean_object*);
static const lean_string_object l_Lean_instToJsonModuleSetup_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "package"};
static const lean_object* l_Lean_instToJsonModuleSetup_toJson___closed__0 = (const lean_object*)&l_Lean_instToJsonModuleSetup_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonModuleSetup_toJson(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__9(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instToJsonModuleSetup___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonModuleSetup_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonModuleSetup___closed__0 = (const lean_object*)&l_Lean_instToJsonModuleSetup___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonModuleSetup = (const lean_object*)&l_Lean_instToJsonModuleSetup___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "invalid LeanOptionValue type"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__0_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__0_value)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[anonymous]"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "expected a `Name`, got '"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__4 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__4_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13(lean_object*, lean_object*);
static const lean_string_object l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "expected a `NameMap`, got '"};
static const lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8___closed__0 = (const lean_object*)&l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_instFromJsonModuleSetup_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ModuleSetup"};
static const lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__0 = (const lean_object*)&l_Lean_instFromJsonModuleSetup_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_instFromJsonModuleSetup_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instFromJsonImport_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instFromJsonModuleSetup_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instFromJsonModuleSetup_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_instFromJsonModuleSetup_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 64, 202, 162, 98, 178, 7, 223)}};
static const lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__1 = (const lean_object*)&l_Lean_instFromJsonModuleSetup_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__2;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__3;
static const lean_ctor_object l_Lean_instFromJsonModuleSetup_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__4 = (const lean_object*)&l_Lean_instFromJsonModuleSetup_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__5;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__6;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__7;
static const lean_ctor_object l_Lean_instFromJsonModuleSetup_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(239, 57, 171, 107, 197, 3, 150, 70)}};
static const lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__8 = (const lean_object*)&l_Lean_instFromJsonModuleSetup_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__9;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__10;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__11;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__12;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__13;
static const lean_ctor_object l_Lean_instFromJsonModuleSetup_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(153, 81, 37, 165, 199, 31, 78, 23)}};
static const lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__14 = (const lean_object*)&l_Lean_instFromJsonModuleSetup_fromJson___closed__14_value;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__15;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__16;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__17;
static const lean_ctor_object l_Lean_instFromJsonModuleSetup_fromJson___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(18, 147, 162, 154, 39, 2, 76, 131)}};
static const lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__18 = (const lean_object*)&l_Lean_instFromJsonModuleSetup_fromJson___closed__18_value;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__19;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__20;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__21;
static const lean_ctor_object l_Lean_instFromJsonModuleSetup_fromJson___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(213, 126, 44, 113, 100, 173, 176, 199)}};
static const lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__22 = (const lean_object*)&l_Lean_instFromJsonModuleSetup_fromJson___closed__22_value;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__23;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__24;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__25;
static const lean_ctor_object l_Lean_instFromJsonModuleSetup_fromJson___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__14_value),LEAN_SCALAR_PTR_LITERAL(43, 100, 103, 72, 156, 88, 10, 236)}};
static const lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__26 = (const lean_object*)&l_Lean_instFromJsonModuleSetup_fromJson___closed__26_value;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__27;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__28;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__29;
static const lean_ctor_object l_Lean_instFromJsonModuleSetup_fromJson___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleSetup_repr___redArg___closed__16_value),LEAN_SCALAR_PTR_LITERAL(15, 45, 121, 141, 112, 165, 100, 9)}};
static const lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__30 = (const lean_object*)&l_Lean_instFromJsonModuleSetup_fromJson___closed__30_value;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__31;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__32;
static lean_once_cell_t l_Lean_instFromJsonModuleSetup_fromJson___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleSetup_fromJson___closed__33;
LEAN_EXPORT lean_object* l_Lean_instFromJsonModuleSetup_fromJson(lean_object*);
static const lean_closure_object l_Lean_instFromJsonModuleSetup___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonModuleSetup_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonModuleSetup___closed__0 = (const lean_object*)&l_Lean_instFromJsonModuleSetup___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonModuleSetup = (const lean_object*)&l_Lean_instFromJsonModuleSetup___closed__0_value;
static const lean_string_object l_Lean_ModuleSetup_load___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "failed to load header from "};
static const lean_object* l_Lean_ModuleSetup_load___closed__0 = (const lean_object*)&l_Lean_ModuleSetup_load___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_ModuleSetup_load(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleSetup_load___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprImport_repr_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Lean_instReprImport_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_unsigned_to_nat(10u);
v___x_17_ = lean_nat_to_int(v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Lean_instReprImport_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = lean_unsigned_to_nat(13u);
v___x_25_ = lean_nat_to_int(v___x_24_);
return v___x_25_;
}
}
static lean_object* _init_l_Lean_instReprImport_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_unsigned_to_nat(14u);
v___x_30_ = lean_nat_to_int(v___x_29_);
return v___x_30_;
}
}
static lean_object* _init_l_Lean_instReprImport_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__0));
v___x_36_ = lean_string_length(v___x_35_);
return v___x_36_;
}
}
static lean_object* _init_l_Lean_instReprImport_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__19, &l_Lean_instReprImport_repr___redArg___closed__19_once, _init_l_Lean_instReprImport_repr___redArg___closed__19);
v___x_38_ = lean_nat_to_int(v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprImport_repr___redArg(lean_object* v_x_43_){
_start:
{
lean_object* v_module_44_; uint8_t v_importAll_45_; uint8_t v_isExported_46_; uint8_t v_isMeta_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; uint8_t v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v_module_44_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_module_44_);
v_importAll_45_ = lean_ctor_get_uint8(v_x_43_, sizeof(void*)*1);
v_isExported_46_ = lean_ctor_get_uint8(v_x_43_, sizeof(void*)*1 + 1);
v_isMeta_47_ = lean_ctor_get_uint8(v_x_43_, sizeof(void*)*1 + 2);
lean_dec_ref(v_x_43_);
v___x_48_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__5));
v___x_49_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__6));
v___x_50_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__7, &l_Lean_instReprImport_repr___redArg___closed__7_once, _init_l_Lean_instReprImport_repr___redArg___closed__7);
v___x_51_ = lean_unsigned_to_nat(0u);
v___x_52_ = l_Lean_Name_reprPrec(v_module_44_, v___x_51_);
v___x_53_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_50_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
v___x_54_ = 0;
v___x_55_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_55_, 0, v___x_53_);
lean_ctor_set_uint8(v___x_55_, sizeof(void*)*1, v___x_54_);
v___x_56_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_49_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v___x_57_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__9));
v___x_58_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_56_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v___x_59_ = lean_box(1);
v___x_60_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_58_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
v___x_61_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__11));
v___x_62_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_60_);
lean_ctor_set(v___x_62_, 1, v___x_61_);
v___x_63_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v___x_48_);
v___x_64_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__12, &l_Lean_instReprImport_repr___redArg___closed__12_once, _init_l_Lean_instReprImport_repr___redArg___closed__12);
v___x_65_ = l_Bool_repr___redArg(v_importAll_45_);
v___x_66_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_64_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
v___x_67_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set_uint8(v___x_67_, sizeof(void*)*1, v___x_54_);
v___x_68_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_63_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_57_);
v___x_70_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v___x_59_);
v___x_71_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__14));
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_70_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_48_);
v___x_74_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__15, &l_Lean_instReprImport_repr___redArg___closed__15_once, _init_l_Lean_instReprImport_repr___redArg___closed__15);
v___x_75_ = l_Bool_repr___redArg(v_isExported_46_);
v___x_76_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_74_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
v___x_77_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set_uint8(v___x_77_, sizeof(void*)*1, v___x_54_);
v___x_78_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_73_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
v___x_79_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___x_57_);
v___x_80_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_59_);
v___x_81_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__17));
v___x_82_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_80_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___x_48_);
v___x_84_ = l_Bool_repr___redArg(v_isMeta_47_);
v___x_85_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_50_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*1, v___x_54_);
v___x_87_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_83_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__20, &l_Lean_instReprImport_repr___redArg___closed__20_once, _init_l_Lean_instReprImport_repr___redArg___closed__20);
v___x_89_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__21));
v___x_90_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v___x_87_);
v___x_91_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__22));
v___x_92_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_90_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
v___x_93_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_88_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set_uint8(v___x_94_, sizeof(void*)*1, v___x_54_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprImport_repr(lean_object* v_x_95_, lean_object* v_prec_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_instReprImport_repr___redArg(v_x_95_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprImport_repr___boxed(lean_object* v_x_98_, lean_object* v_prec_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_instReprImport_repr(v_x_98_, v_prec_99_);
lean_dec(v_prec_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
if (lean_obj_tag(v_a_109_) == 0)
{
lean_object* v___x_111_; 
v___x_111_ = lean_array_to_list(v_a_110_);
return v___x_111_;
}
else
{
lean_object* v_head_112_; lean_object* v_tail_113_; lean_object* v___x_114_; 
v_head_112_ = lean_ctor_get(v_a_109_, 0);
lean_inc(v_head_112_);
v_tail_113_ = lean_ctor_get(v_a_109_, 1);
lean_inc(v_tail_113_);
lean_dec_ref_known(v_a_109_, 2);
v___x_114_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_110_, v_head_112_);
v_a_109_ = v_tail_113_;
v_a_110_ = v___x_114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonImport_toJson(lean_object* v_x_118_){
_start:
{
lean_object* v_module_119_; uint8_t v_importAll_120_; uint8_t v_isExported_121_; uint8_t v_isMeta_122_; lean_object* v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v_module_119_ = lean_ctor_get(v_x_118_, 0);
lean_inc(v_module_119_);
v_importAll_120_ = lean_ctor_get_uint8(v_x_118_, sizeof(void*)*1);
v_isExported_121_ = lean_ctor_get_uint8(v_x_118_, sizeof(void*)*1 + 1);
v_isMeta_122_ = lean_ctor_get_uint8(v_x_118_, sizeof(void*)*1 + 2);
lean_dec_ref(v_x_118_);
v___x_123_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__1));
v___x_124_ = 1;
v___x_125_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_119_, v___x_124_);
v___x_126_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_123_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = lean_box(0);
v___x_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__10));
v___x_131_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_131_, 0, v_importAll_120_);
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_130_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v___x_133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v___x_128_);
v___x_134_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__13));
v___x_135_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_135_, 0, v_isExported_121_);
v___x_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_134_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___x_128_);
v___x_138_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__16));
v___x_139_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_139_, 0, v_isMeta_122_);
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_138_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v___x_128_);
v___x_142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v___x_128_);
v___x_143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_137_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v___x_144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_133_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v___x_145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_129_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
v___x_146_ = ((lean_object*)(l_Lean_instToJsonImport_toJson___closed__0));
v___x_147_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(v___x_145_, v___x_146_);
v___x_148_ = l_Lean_Json_mkObj(v___x_147_);
lean_dec(v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__0(lean_object* v_j_151_, lean_object* v_k_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = l_Lean_Json_getObjValD(v_j_151_, v_k_152_);
v___x_154_ = l_Lean_Name_fromJson_x3f(v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__0___boxed(lean_object* v_j_155_, lean_object* v_k_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__0(v_j_155_, v_k_156_);
lean_dec_ref(v_k_156_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(lean_object* v_j_158_, lean_object* v_k_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = l_Lean_Json_getObjValD(v_j_158_, v_k_159_);
v___x_161_ = l_Lean_Json_getBool_x3f(v___x_160_);
lean_dec(v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1___boxed(lean_object* v_j_162_, lean_object* v_k_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(v_j_162_, v_k_163_);
lean_dec_ref(v_k_163_);
return v_res_164_;
}
}
static lean_object* _init_l_Lean_instFromJsonImport_fromJson___closed__3(void){
_start:
{
uint8_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = 1;
v___x_171_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__2));
v___x_172_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_171_, v___x_170_);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_instFromJsonImport_fromJson___closed__5(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__4));
v___x_175_ = lean_obj_once(&l_Lean_instFromJsonImport_fromJson___closed__3, &l_Lean_instFromJsonImport_fromJson___closed__3_once, _init_l_Lean_instFromJsonImport_fromJson___closed__3);
v___x_176_ = lean_string_append(v___x_175_, v___x_174_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_instFromJsonImport_fromJson___closed__7(void){
_start:
{
uint8_t v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = 1;
v___x_180_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__6));
v___x_181_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_180_, v___x_179_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_instFromJsonImport_fromJson___closed__8(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = lean_obj_once(&l_Lean_instFromJsonImport_fromJson___closed__7, &l_Lean_instFromJsonImport_fromJson___closed__7_once, _init_l_Lean_instFromJsonImport_fromJson___closed__7);
v___x_183_ = lean_obj_once(&l_Lean_instFromJsonImport_fromJson___closed__5, &l_Lean_instFromJsonImport_fromJson___closed__5_once, _init_l_Lean_instFromJsonImport_fromJson___closed__5);
v___x_184_ = lean_string_append(v___x_183_, v___x_182_);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_instFromJsonImport_fromJson___closed__10(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_187_ = lean_obj_once(&l_Lean_instFromJsonImport_fromJson___closed__8, &l_Lean_instFromJsonImport_fromJson___closed__8_once, _init_l_Lean_instFromJsonImport_fromJson___closed__8);
v___x_188_ = lean_string_append(v___x_187_, v___x_186_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_instFromJsonImport_fromJson___closed__12(void){
_start:
{
uint8_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = 1;
v___x_192_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__11));
v___x_193_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_192_, v___x_191_);
return v___x_193_;
}
}
static lean_object* _init_l_Lean_instFromJsonImport_fromJson___closed__13(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = lean_obj_once(&l_Lean_instFromJsonImport_fromJson___closed__12, &l_Lean_instFromJsonImport_fromJson___closed__12_once, _init_l_Lean_instFromJsonImport_fromJson___closed__12);
v___x_195_ = lean_obj_once(&l_Lean_instFromJsonImport_fromJson___closed__5, &l_Lean_instFromJsonImport_fromJson___closed__5_once, _init_l_Lean_instFromJsonImport_fromJson___closed__5);
v___x_196_ = lean_string_append(v___x_195_, v___x_194_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_instFromJsonImport_fromJson___closed__14(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_198_ = lean_obj_once(&l_Lean_instFromJsonImport_fromJson___closed__13, &l_Lean_instFromJsonImport_fromJson___closed__13_once, _init_l_Lean_instFromJsonImport_fromJson___closed__13);
v___x_199_ = lean_string_append(v___x_198_, v___x_197_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_instFromJsonImport_fromJson___closed__16(void){
_start:
{
uint8_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = 1;
v___x_203_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__15));
v___x_204_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_203_, v___x_202_);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_instFromJsonImport_fromJson___closed__17(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = lean_obj_once(&l_Lean_instFromJsonImport_fromJson___closed__16, &l_Lean_instFromJsonImport_fromJson___closed__16_once, _init_l_Lean_instFromJsonImport_fromJson___closed__16);
v___x_206_ = lean_obj_once(&l_Lean_instFromJsonImport_fromJson___closed__5, &l_Lean_instFromJsonImport_fromJson___closed__5_once, _init_l_Lean_instFromJsonImport_fromJson___closed__5);
v___x_207_ = lean_string_append(v___x_206_, v___x_205_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_instFromJsonImport_fromJson___closed__18(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_209_ = lean_obj_once(&l_Lean_instFromJsonImport_fromJson___closed__17, &l_Lean_instFromJsonImport_fromJson___closed__17_once, _init_l_Lean_instFromJsonImport_fromJson___closed__17);
v___x_210_ = lean_string_append(v___x_209_, v___x_208_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_instFromJsonImport_fromJson___closed__20(void){
_start:
{
uint8_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = 1;
v___x_214_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__19));
v___x_215_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_214_, v___x_213_);
return v___x_215_;
}
}
static lean_object* _init_l_Lean_instFromJsonImport_fromJson___closed__21(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = lean_obj_once(&l_Lean_instFromJsonImport_fromJson___closed__20, &l_Lean_instFromJsonImport_fromJson___closed__20_once, _init_l_Lean_instFromJsonImport_fromJson___closed__20);
v___x_217_ = lean_obj_once(&l_Lean_instFromJsonImport_fromJson___closed__5, &l_Lean_instFromJsonImport_fromJson___closed__5_once, _init_l_Lean_instFromJsonImport_fromJson___closed__5);
v___x_218_ = lean_string_append(v___x_217_, v___x_216_);
return v___x_218_;
}
}
static lean_object* _init_l_Lean_instFromJsonImport_fromJson___closed__22(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_220_ = lean_obj_once(&l_Lean_instFromJsonImport_fromJson___closed__21, &l_Lean_instFromJsonImport_fromJson___closed__21_once, _init_l_Lean_instFromJsonImport_fromJson___closed__21);
v___x_221_ = lean_string_append(v___x_220_, v___x_219_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonImport_fromJson(lean_object* v_json_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__1));
lean_inc(v_json_222_);
v___x_224_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__0(v_json_222_, v___x_223_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_234_; 
lean_dec(v_json_222_);
v_a_225_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_234_ == 0)
{
v___x_227_ = v___x_224_;
v_isShared_228_ = v_isSharedCheck_234_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_224_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_234_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_229_ = lean_obj_once(&l_Lean_instFromJsonImport_fromJson___closed__10, &l_Lean_instFromJsonImport_fromJson___closed__10_once, _init_l_Lean_instFromJsonImport_fromJson___closed__10);
v___x_230_ = lean_string_append(v___x_229_, v_a_225_);
lean_dec(v_a_225_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_230_);
v___x_232_ = v___x_227_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
else
{
lean_object* v_a_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v_a_235_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_235_);
lean_dec_ref_known(v___x_224_, 1);
v___x_236_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__10));
lean_inc(v_json_222_);
v___x_237_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(v_json_222_, v___x_236_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_247_; 
lean_dec(v_a_235_);
lean_dec(v_json_222_);
v_a_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_247_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_247_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_247_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_242_ = lean_obj_once(&l_Lean_instFromJsonImport_fromJson___closed__14, &l_Lean_instFromJsonImport_fromJson___closed__14_once, _init_l_Lean_instFromJsonImport_fromJson___closed__14);
v___x_243_ = lean_string_append(v___x_242_, v_a_238_);
lean_dec(v_a_238_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_243_);
v___x_245_ = v___x_240_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_243_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
else
{
lean_object* v_a_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_a_248_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_248_);
lean_dec_ref_known(v___x_237_, 1);
v___x_249_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__13));
lean_inc(v_json_222_);
v___x_250_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(v_json_222_, v___x_249_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_260_; 
lean_dec(v_a_248_);
lean_dec(v_a_235_);
lean_dec(v_json_222_);
v_a_251_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_260_ == 0)
{
v___x_253_ = v___x_250_;
v_isShared_254_ = v_isSharedCheck_260_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_250_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_260_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_255_ = lean_obj_once(&l_Lean_instFromJsonImport_fromJson___closed__18, &l_Lean_instFromJsonImport_fromJson___closed__18_once, _init_l_Lean_instFromJsonImport_fromJson___closed__18);
v___x_256_ = lean_string_append(v___x_255_, v_a_251_);
lean_dec(v_a_251_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 0, v___x_256_);
v___x_258_ = v___x_253_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_a_261_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_261_);
lean_dec_ref_known(v___x_250_, 1);
v___x_262_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__16));
v___x_263_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(v_json_222_, v___x_262_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_273_; 
lean_dec(v_a_261_);
lean_dec(v_a_248_);
lean_dec(v_a_235_);
v_a_264_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_273_ == 0)
{
v___x_266_ = v___x_263_;
v_isShared_267_ = v_isSharedCheck_273_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_263_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_273_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_268_ = lean_obj_once(&l_Lean_instFromJsonImport_fromJson___closed__22, &l_Lean_instFromJsonImport_fromJson___closed__22_once, _init_l_Lean_instFromJsonImport_fromJson___closed__22);
v___x_269_ = lean_string_append(v___x_268_, v_a_264_);
lean_dec(v_a_264_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_269_);
v___x_271_ = v___x_266_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_285_; 
v_a_274_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_285_ == 0)
{
v___x_276_ = v___x_263_;
v_isShared_277_ = v_isSharedCheck_285_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_263_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_285_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; uint8_t v___x_279_; uint8_t v___x_280_; uint8_t v___x_281_; lean_object* v___x_283_; 
v___x_278_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_278_, 0, v_a_235_);
v___x_279_ = lean_unbox(v_a_248_);
lean_dec(v_a_248_);
lean_ctor_set_uint8(v___x_278_, sizeof(void*)*1, v___x_279_);
v___x_280_ = lean_unbox(v_a_261_);
lean_dec(v_a_261_);
lean_ctor_set_uint8(v___x_278_, sizeof(void*)*1 + 1, v___x_280_);
v___x_281_ = lean_unbox(v_a_274_);
lean_dec(v_a_274_);
lean_ctor_set_uint8(v___x_278_, sizeof(void*)*1 + 2, v___x_281_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_278_);
v___x_283_ = v___x_276_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqImport_beq(lean_object* v_x_288_, lean_object* v_x_289_){
_start:
{
lean_object* v_module_290_; uint8_t v_importAll_291_; uint8_t v_isExported_292_; uint8_t v_isMeta_293_; lean_object* v_module_294_; uint8_t v_importAll_295_; uint8_t v_isExported_296_; uint8_t v_isMeta_297_; uint8_t v___y_299_; uint8_t v___y_301_; uint8_t v___x_302_; 
v_module_290_ = lean_ctor_get(v_x_288_, 0);
v_importAll_291_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*1);
v_isExported_292_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*1 + 1);
v_isMeta_293_ = lean_ctor_get_uint8(v_x_288_, sizeof(void*)*1 + 2);
v_module_294_ = lean_ctor_get(v_x_289_, 0);
v_importAll_295_ = lean_ctor_get_uint8(v_x_289_, sizeof(void*)*1);
v_isExported_296_ = lean_ctor_get_uint8(v_x_289_, sizeof(void*)*1 + 1);
v_isMeta_297_ = lean_ctor_get_uint8(v_x_289_, sizeof(void*)*1 + 2);
v___x_302_ = lean_name_eq(v_module_290_, v_module_294_);
if (v___x_302_ == 0)
{
return v___x_302_;
}
else
{
if (v_importAll_295_ == 0)
{
if (v_importAll_291_ == 0)
{
v___y_301_ = v___x_302_;
goto v___jp_300_;
}
else
{
return v_importAll_295_;
}
}
else
{
if (v_importAll_291_ == 0)
{
return v_importAll_291_;
}
else
{
v___y_301_ = v_importAll_291_;
goto v___jp_300_;
}
}
}
v___jp_298_:
{
if (v_isMeta_297_ == 0)
{
if (v_isMeta_293_ == 0)
{
return v___y_299_;
}
else
{
return v_isMeta_297_;
}
}
else
{
return v_isMeta_293_;
}
}
v___jp_300_:
{
if (v_isExported_296_ == 0)
{
if (v_isExported_292_ == 0)
{
v___y_299_ = v___y_301_;
goto v___jp_298_;
}
else
{
return v_isExported_296_;
}
}
else
{
if (v_isExported_292_ == 0)
{
return v_isExported_292_;
}
else
{
v___y_299_ = v_isExported_292_;
goto v___jp_298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqImport_beq___boxed(lean_object* v_x_303_, lean_object* v_x_304_){
_start:
{
uint8_t v_res_305_; lean_object* v_r_306_; 
v_res_305_ = l_Lean_instBEqImport_beq(v_x_303_, v_x_304_);
lean_dec_ref(v_x_304_);
lean_dec_ref(v_x_303_);
v_r_306_ = lean_box(v_res_305_);
return v_r_306_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableImport_hash(lean_object* v_x_309_){
_start:
{
lean_object* v_module_310_; uint8_t v_importAll_311_; uint8_t v_isExported_312_; uint8_t v_isMeta_313_; uint64_t v___y_315_; uint64_t v___y_316_; uint64_t v___y_323_; uint64_t v___y_324_; uint64_t v___x_328_; uint64_t v___y_330_; 
v_module_310_ = lean_ctor_get(v_x_309_, 0);
v_importAll_311_ = lean_ctor_get_uint8(v_x_309_, sizeof(void*)*1);
v_isExported_312_ = lean_ctor_get_uint8(v_x_309_, sizeof(void*)*1 + 1);
v_isMeta_313_ = lean_ctor_get_uint8(v_x_309_, sizeof(void*)*1 + 2);
v___x_328_ = 0ULL;
if (lean_obj_tag(v_module_310_) == 0)
{
uint64_t v___x_334_; 
v___x_334_ = 1723ULL;
v___y_330_ = v___x_334_;
goto v___jp_329_;
}
else
{
uint64_t v_hash_335_; 
v_hash_335_ = lean_ctor_get_uint64(v_module_310_, sizeof(void*)*2);
v___y_330_ = v_hash_335_;
goto v___jp_329_;
}
v___jp_314_:
{
uint64_t v___x_317_; 
v___x_317_ = lean_uint64_mix_hash(v___y_315_, v___y_316_);
if (v_isMeta_313_ == 0)
{
uint64_t v___x_318_; uint64_t v___x_319_; 
v___x_318_ = 13ULL;
v___x_319_ = lean_uint64_mix_hash(v___x_317_, v___x_318_);
return v___x_319_;
}
else
{
uint64_t v___x_320_; uint64_t v___x_321_; 
v___x_320_ = 11ULL;
v___x_321_ = lean_uint64_mix_hash(v___x_317_, v___x_320_);
return v___x_321_;
}
}
v___jp_322_:
{
uint64_t v___x_325_; 
v___x_325_ = lean_uint64_mix_hash(v___y_323_, v___y_324_);
if (v_isExported_312_ == 0)
{
uint64_t v___x_326_; 
v___x_326_ = 13ULL;
v___y_315_ = v___x_325_;
v___y_316_ = v___x_326_;
goto v___jp_314_;
}
else
{
uint64_t v___x_327_; 
v___x_327_ = 11ULL;
v___y_315_ = v___x_325_;
v___y_316_ = v___x_327_;
goto v___jp_314_;
}
}
v___jp_329_:
{
uint64_t v___x_331_; 
v___x_331_ = lean_uint64_mix_hash(v___x_328_, v___y_330_);
if (v_importAll_311_ == 0)
{
uint64_t v___x_332_; 
v___x_332_ = 13ULL;
v___y_323_ = v___x_331_;
v___y_324_ = v___x_332_;
goto v___jp_322_;
}
else
{
uint64_t v___x_333_; 
v___x_333_ = 11ULL;
v___y_323_ = v___x_331_;
v___y_324_ = v___x_333_;
goto v___jp_322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableImport_hash___boxed(lean_object* v_x_336_){
_start:
{
uint64_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l_Lean_instHashableImport_hash(v_x_336_);
lean_dec_ref(v_x_336_);
v_r_338_ = lean_box_uint64(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Idbg_idbgClientLoop___boxed(lean_object* v_00_u03b1_347_, lean_object* v_inst_00___x40_Lean_Setup_1068012781____hygCtx___hyg_348_, lean_object* v_siteId_349_, lean_object* v_imports_350_, lean_object* v_apply_351_, lean_object* v_a_00___x40___internal___hyg_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = lean_idbg_client_loop(v_siteId_349_, v_imports_350_, v_apply_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeNameImport___lam__0(lean_object* v_x_354_){
_start:
{
uint8_t v___x_355_; uint8_t v___x_356_; lean_object* v___x_357_; 
v___x_355_ = 0;
v___x_356_ = 1;
v___x_357_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_357_, 0, v_x_354_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*1, v___x_355_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*1 + 1, v___x_356_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*1 + 2, v___x_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringImport___lam__0(lean_object* v_imp_365_){
_start:
{
lean_object* v_module_366_; uint8_t v_importAll_367_; uint8_t v_isExported_368_; uint8_t v_isMeta_369_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_386_; 
v_module_366_ = lean_ctor_get(v_imp_365_, 0);
lean_inc(v_module_366_);
v_importAll_367_ = lean_ctor_get_uint8(v_imp_365_, sizeof(void*)*1);
v_isExported_368_ = lean_ctor_get_uint8(v_imp_365_, sizeof(void*)*1 + 1);
v_isMeta_369_ = lean_ctor_get_uint8(v_imp_365_, sizeof(void*)*1 + 2);
lean_dec_ref(v_imp_365_);
if (v_isExported_368_ == 0)
{
lean_object* v___x_389_; 
v___x_389_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__1));
v___y_386_ = v___x_389_;
goto v___jp_385_;
}
else
{
lean_object* v___x_390_; 
v___x_390_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__4));
v___y_386_ = v___x_390_;
goto v___jp_385_;
}
v___jp_370_:
{
lean_object* v___x_373_; uint8_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_373_ = lean_string_append(v___y_371_, v___y_372_);
v___x_374_ = 1;
v___x_375_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_366_, v___x_374_);
v___x_376_ = lean_string_append(v___x_373_, v___x_375_);
lean_dec_ref(v___x_375_);
return v___x_376_;
}
v___jp_377_:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
lean_inc_ref(v___y_378_);
v___x_380_ = lean_string_append(v___y_378_, v___y_379_);
v___x_381_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__0));
v___x_382_ = lean_string_append(v___x_380_, v___x_381_);
if (v_importAll_367_ == 0)
{
lean_object* v___x_383_; 
v___x_383_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__1));
v___y_371_ = v___x_382_;
v___y_372_ = v___x_383_;
goto v___jp_370_;
}
else
{
lean_object* v___x_384_; 
v___x_384_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__2));
v___y_371_ = v___x_382_;
v___y_372_ = v___x_384_;
goto v___jp_370_;
}
}
v___jp_385_:
{
if (v_isMeta_369_ == 0)
{
lean_object* v___x_387_; 
v___x_387_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__1));
v___y_378_ = v___y_386_;
v___y_379_ = v___x_387_;
goto v___jp_377_;
}
else
{
lean_object* v___x_388_; 
v___x_388_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__3));
v___y_378_ = v___y_386_;
v___y_379_ = v___x_388_;
goto v___jp_377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorIdx___impl(uint8_t v_x_393_){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_box(v_x_393_);
v___x_395_ = lean_obj_tag_nat(v___x_394_);
lean_dec(v___x_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorIdx___impl___boxed(lean_object* v_x_396_){
_start:
{
uint8_t v_x_4__boxed_397_; lean_object* v_res_398_; 
v_x_4__boxed_397_ = lean_unbox(v_x_396_);
v_res_398_ = l_Lean_IRPhases_ctorIdx___impl(v_x_4__boxed_397_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorElim___redArg(lean_object* v_k_399_){
_start:
{
lean_inc(v_k_399_);
return v_k_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorElim___redArg___boxed(lean_object* v_k_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_IRPhases_ctorElim___redArg(v_k_400_);
lean_dec(v_k_400_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorElim(lean_object* v_motive_402_, lean_object* v_ctorIdx_403_, uint8_t v_t_404_, lean_object* v_h_405_, lean_object* v_k_406_){
_start:
{
lean_inc(v_k_406_);
return v_k_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorElim___boxed(lean_object* v_motive_407_, lean_object* v_ctorIdx_408_, lean_object* v_t_409_, lean_object* v_h_410_, lean_object* v_k_411_){
_start:
{
uint8_t v_t_boxed_412_; lean_object* v_res_413_; 
v_t_boxed_412_ = lean_unbox(v_t_409_);
v_res_413_ = l_Lean_IRPhases_ctorElim(v_motive_407_, v_ctorIdx_408_, v_t_boxed_412_, v_h_410_, v_k_411_);
lean_dec(v_k_411_);
lean_dec(v_ctorIdx_408_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_runtime_elim___redArg(lean_object* v_runtime_414_){
_start:
{
lean_inc(v_runtime_414_);
return v_runtime_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_runtime_elim___redArg___boxed(lean_object* v_runtime_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_IRPhases_runtime_elim___redArg(v_runtime_415_);
lean_dec(v_runtime_415_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_runtime_elim(lean_object* v_motive_417_, uint8_t v_t_418_, lean_object* v_h_419_, lean_object* v_runtime_420_){
_start:
{
lean_inc(v_runtime_420_);
return v_runtime_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_runtime_elim___boxed(lean_object* v_motive_421_, lean_object* v_t_422_, lean_object* v_h_423_, lean_object* v_runtime_424_){
_start:
{
uint8_t v_t_boxed_425_; lean_object* v_res_426_; 
v_t_boxed_425_ = lean_unbox(v_t_422_);
v_res_426_ = l_Lean_IRPhases_runtime_elim(v_motive_421_, v_t_boxed_425_, v_h_423_, v_runtime_424_);
lean_dec(v_runtime_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_comptime_elim___redArg(lean_object* v_comptime_427_){
_start:
{
lean_inc(v_comptime_427_);
return v_comptime_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_comptime_elim___redArg___boxed(lean_object* v_comptime_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_IRPhases_comptime_elim___redArg(v_comptime_428_);
lean_dec(v_comptime_428_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_comptime_elim(lean_object* v_motive_430_, uint8_t v_t_431_, lean_object* v_h_432_, lean_object* v_comptime_433_){
_start:
{
lean_inc(v_comptime_433_);
return v_comptime_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_comptime_elim___boxed(lean_object* v_motive_434_, lean_object* v_t_435_, lean_object* v_h_436_, lean_object* v_comptime_437_){
_start:
{
uint8_t v_t_boxed_438_; lean_object* v_res_439_; 
v_t_boxed_438_ = lean_unbox(v_t_435_);
v_res_439_ = l_Lean_IRPhases_comptime_elim(v_motive_434_, v_t_boxed_438_, v_h_436_, v_comptime_437_);
lean_dec(v_comptime_437_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_all_elim___redArg(lean_object* v_all_440_){
_start:
{
lean_inc(v_all_440_);
return v_all_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_all_elim___redArg___boxed(lean_object* v_all_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_IRPhases_all_elim___redArg(v_all_441_);
lean_dec(v_all_441_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_all_elim(lean_object* v_motive_443_, uint8_t v_t_444_, lean_object* v_h_445_, lean_object* v_all_446_){
_start:
{
lean_inc(v_all_446_);
return v_all_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_all_elim___boxed(lean_object* v_motive_447_, lean_object* v_t_448_, lean_object* v_h_449_, lean_object* v_all_450_){
_start:
{
uint8_t v_t_boxed_451_; lean_object* v_res_452_; 
v_t_boxed_451_ = lean_unbox(v_t_448_);
v_res_452_ = l_Lean_IRPhases_all_elim(v_motive_447_, v_t_boxed_451_, v_h_449_, v_all_450_);
lean_dec(v_all_450_);
return v_res_452_;
}
}
static uint8_t _init_l_Lean_instInhabitedIRPhases_default(void){
_start:
{
uint8_t v___x_453_; 
v___x_453_ = 0;
return v___x_453_;
}
}
static uint8_t _init_l_Lean_instInhabitedIRPhases(void){
_start:
{
uint8_t v___x_454_; 
v___x_454_ = 0;
return v___x_454_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqIRPhases_beq(uint8_t v_x_455_, uint8_t v_y_456_){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_457_ = lean_box(v_x_455_);
v___x_458_ = lean_obj_tag_nat(v___x_457_);
lean_dec(v___x_457_);
v___x_459_ = lean_box(v_y_456_);
v___x_460_ = lean_obj_tag_nat(v___x_459_);
lean_dec(v___x_459_);
v___x_461_ = lean_nat_dec_eq(v___x_458_, v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqIRPhases_beq___boxed(lean_object* v_x_462_, lean_object* v_y_463_){
_start:
{
uint8_t v_x_24__boxed_464_; uint8_t v_y_25__boxed_465_; uint8_t v_res_466_; lean_object* v_r_467_; 
v_x_24__boxed_464_ = lean_unbox(v_x_462_);
v_y_25__boxed_465_ = lean_unbox(v_y_463_);
v_res_466_ = l_Lean_instBEqIRPhases_beq(v_x_24__boxed_464_, v_y_25__boxed_465_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
static lean_object* _init_l_Lean_instReprIRPhases_repr___closed__6(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_unsigned_to_nat(2u);
v___x_480_ = lean_nat_to_int(v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_instReprIRPhases_repr___closed__7(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_unsigned_to_nat(1u);
v___x_482_ = lean_nat_to_int(v___x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprIRPhases_repr(uint8_t v_x_483_, lean_object* v_prec_484_){
_start:
{
lean_object* v___y_486_; lean_object* v___y_493_; lean_object* v___y_500_; 
switch(v_x_483_)
{
case 0:
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = lean_unsigned_to_nat(1024u);
v___x_507_ = lean_nat_dec_le(v___x_506_, v_prec_484_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
v___x_508_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__6, &l_Lean_instReprIRPhases_repr___closed__6_once, _init_l_Lean_instReprIRPhases_repr___closed__6);
v___y_486_ = v___x_508_;
goto v___jp_485_;
}
else
{
lean_object* v___x_509_; 
v___x_509_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__7, &l_Lean_instReprIRPhases_repr___closed__7_once, _init_l_Lean_instReprIRPhases_repr___closed__7);
v___y_486_ = v___x_509_;
goto v___jp_485_;
}
}
case 1:
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = lean_unsigned_to_nat(1024u);
v___x_511_ = lean_nat_dec_le(v___x_510_, v_prec_484_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; 
v___x_512_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__6, &l_Lean_instReprIRPhases_repr___closed__6_once, _init_l_Lean_instReprIRPhases_repr___closed__6);
v___y_493_ = v___x_512_;
goto v___jp_492_;
}
else
{
lean_object* v___x_513_; 
v___x_513_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__7, &l_Lean_instReprIRPhases_repr___closed__7_once, _init_l_Lean_instReprIRPhases_repr___closed__7);
v___y_493_ = v___x_513_;
goto v___jp_492_;
}
}
default: 
{
lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_514_ = lean_unsigned_to_nat(1024u);
v___x_515_ = lean_nat_dec_le(v___x_514_, v_prec_484_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; 
v___x_516_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__6, &l_Lean_instReprIRPhases_repr___closed__6_once, _init_l_Lean_instReprIRPhases_repr___closed__6);
v___y_500_ = v___x_516_;
goto v___jp_499_;
}
else
{
lean_object* v___x_517_; 
v___x_517_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__7, &l_Lean_instReprIRPhases_repr___closed__7_once, _init_l_Lean_instReprIRPhases_repr___closed__7);
v___y_500_ = v___x_517_;
goto v___jp_499_;
}
}
}
v___jp_485_:
{
lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_487_ = ((lean_object*)(l_Lean_instReprIRPhases_repr___closed__1));
lean_inc(v___y_486_);
v___x_488_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_488_, 0, v___y_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = 0;
v___x_490_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_490_, 0, v___x_488_);
lean_ctor_set_uint8(v___x_490_, sizeof(void*)*1, v___x_489_);
v___x_491_ = l_Repr_addAppParen(v___x_490_, v_prec_484_);
return v___x_491_;
}
v___jp_492_:
{
lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_494_ = ((lean_object*)(l_Lean_instReprIRPhases_repr___closed__3));
lean_inc(v___y_493_);
v___x_495_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_495_, 0, v___y_493_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
v___x_496_ = 0;
v___x_497_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_497_, 0, v___x_495_);
lean_ctor_set_uint8(v___x_497_, sizeof(void*)*1, v___x_496_);
v___x_498_ = l_Repr_addAppParen(v___x_497_, v_prec_484_);
return v___x_498_;
}
v___jp_499_:
{
lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_501_ = ((lean_object*)(l_Lean_instReprIRPhases_repr___closed__5));
lean_inc(v___y_500_);
v___x_502_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_502_, 0, v___y_500_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
v___x_503_ = 0;
v___x_504_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_504_, 0, v___x_502_);
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*1, v___x_503_);
v___x_505_ = l_Repr_addAppParen(v___x_504_, v_prec_484_);
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprIRPhases_repr___boxed(lean_object* v_x_518_, lean_object* v_prec_519_){
_start:
{
uint8_t v_x_171__boxed_520_; lean_object* v_res_521_; 
v_x_171__boxed_520_ = lean_unbox(v_x_518_);
v_res_521_ = l_Lean_instReprIRPhases_repr(v_x_171__boxed_520_, v_prec_519_);
lean_dec(v_prec_519_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_524_, lean_object* v_x_525_, lean_object* v_x_526_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
lean_dec(v_x_524_);
return v_x_525_;
}
else
{
lean_object* v_head_527_; lean_object* v_tail_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_538_; 
v_head_527_ = lean_ctor_get(v_x_526_, 0);
v_tail_528_ = lean_ctor_get(v_x_526_, 1);
v_isSharedCheck_538_ = !lean_is_exclusive(v_x_526_);
if (v_isSharedCheck_538_ == 0)
{
v___x_530_ = v_x_526_;
v_isShared_531_ = v_isSharedCheck_538_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_tail_528_);
lean_inc(v_head_527_);
lean_dec(v_x_526_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_538_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
lean_inc(v_x_524_);
if (v_isShared_531_ == 0)
{
lean_ctor_set_tag(v___x_530_, 5);
lean_ctor_set(v___x_530_, 1, v_x_524_);
lean_ctor_set(v___x_530_, 0, v_x_525_);
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_x_525_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_x_524_);
v___x_533_ = v_reuseFailAlloc_537_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = l_Lean_instReprImport_repr___redArg(v_head_527_);
v___x_535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v_x_525_ = v___x_535_;
v_x_526_ = v_tail_528_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0_spec__1(lean_object* v_x_539_, lean_object* v_x_540_, lean_object* v_x_541_){
_start:
{
if (lean_obj_tag(v_x_541_) == 0)
{
lean_dec(v_x_539_);
return v_x_540_;
}
else
{
lean_object* v_head_542_; lean_object* v_tail_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_553_; 
v_head_542_ = lean_ctor_get(v_x_541_, 0);
v_tail_543_ = lean_ctor_get(v_x_541_, 1);
v_isSharedCheck_553_ = !lean_is_exclusive(v_x_541_);
if (v_isSharedCheck_553_ == 0)
{
v___x_545_ = v_x_541_;
v_isShared_546_ = v_isSharedCheck_553_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_tail_543_);
lean_inc(v_head_542_);
lean_dec(v_x_541_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_553_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
lean_inc(v_x_539_);
if (v_isShared_546_ == 0)
{
lean_ctor_set_tag(v___x_545_, 5);
lean_ctor_set(v___x_545_, 1, v_x_539_);
lean_ctor_set(v___x_545_, 0, v_x_540_);
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_x_540_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_x_539_);
v___x_548_ = v_reuseFailAlloc_552_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_549_ = l_Lean_instReprImport_repr___redArg(v_head_542_);
v___x_550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0_spec__1_spec__2(v_x_539_, v___x_550_, v_tail_543_);
return v___x_551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0(lean_object* v_x_554_, lean_object* v_x_555_){
_start:
{
if (lean_obj_tag(v_x_554_) == 0)
{
lean_object* v___x_556_; 
lean_dec(v_x_555_);
v___x_556_ = lean_box(0);
return v___x_556_;
}
else
{
lean_object* v_tail_557_; 
v_tail_557_ = lean_ctor_get(v_x_554_, 1);
if (lean_obj_tag(v_tail_557_) == 0)
{
lean_object* v_head_558_; lean_object* v___x_559_; 
lean_dec(v_x_555_);
v_head_558_ = lean_ctor_get(v_x_554_, 0);
lean_inc(v_head_558_);
lean_dec_ref_known(v_x_554_, 2);
v___x_559_ = l_Lean_instReprImport_repr___redArg(v_head_558_);
return v___x_559_;
}
else
{
lean_object* v_head_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
lean_inc(v_tail_557_);
v_head_560_ = lean_ctor_get(v_x_554_, 0);
lean_inc(v_head_560_);
lean_dec_ref_known(v_x_554_, 2);
v___x_561_ = l_Lean_instReprImport_repr___redArg(v_head_560_);
v___x_562_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0_spec__1(v_x_555_, v___x_561_, v_tail_557_);
return v___x_562_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__0));
v___x_569_ = lean_string_length(v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_obj_once(&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3, &l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3);
v___x_571_ = lean_nat_to_int(v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0(lean_object* v_xs_579_){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_580_ = lean_array_get_size(v_xs_579_);
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = lean_nat_dec_eq(v___x_580_, v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_583_ = lean_array_to_list(v_xs_579_);
v___x_584_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_585_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0(v___x_583_, v___x_584_);
v___x_586_ = lean_obj_once(&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4);
v___x_587_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5));
v___x_588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v___x_585_);
v___x_589_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6));
v___x_590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_586_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = l_Std_Format_fill(v___x_591_);
return v___x_592_;
}
else
{
lean_object* v___x_593_; 
lean_dec_ref(v_xs_579_);
v___x_593_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8));
return v___x_593_;
}
}
}
static lean_object* _init_l_Lean_instReprModuleHeader_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_unsigned_to_nat(11u);
v___x_604_ = lean_nat_to_int(v___x_603_);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_instReprModuleHeader_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_unsigned_to_nat(12u);
v___x_609_ = lean_nat_to_int(v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleHeader_repr___redArg(lean_object* v_x_610_){
_start:
{
lean_object* v_imports_611_; uint8_t v_isModule_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_645_; 
v_imports_611_ = lean_ctor_get(v_x_610_, 0);
v_isModule_612_ = lean_ctor_get_uint8(v_x_610_, sizeof(void*)*1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_x_610_);
if (v_isSharedCheck_645_ == 0)
{
v___x_614_ = v_x_610_;
v_isShared_615_ = v_isSharedCheck_645_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_imports_611_);
lean_dec(v_x_610_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_645_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; lean_object* v___x_623_; 
v___x_616_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__5));
v___x_617_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__3));
v___x_618_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__4, &l_Lean_instReprModuleHeader_repr___redArg___closed__4_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__4);
v___x_619_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0(v_imports_611_);
v___x_620_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = 0;
if (v_isShared_615_ == 0)
{
lean_ctor_set_tag(v___x_614_, 6);
lean_ctor_set(v___x_614_, 0, v___x_620_);
v___x_623_ = v___x_614_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_620_);
v___x_623_ = v_reuseFailAlloc_644_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
lean_ctor_set_uint8(v___x_623_, sizeof(void*)*1, v___x_621_);
v___x_624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_617_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__9));
v___x_626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = lean_box(1);
v___x_628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_626_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__6));
v___x_630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v___x_616_);
v___x_632_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__7, &l_Lean_instReprModuleHeader_repr___redArg___closed__7_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__7);
v___x_633_ = l_Bool_repr___redArg(v_isModule_612_);
v___x_634_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set_uint8(v___x_635_, sizeof(void*)*1, v___x_621_);
v___x_636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_631_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__20, &l_Lean_instReprImport_repr___redArg___closed__20_once, _init_l_Lean_instReprImport_repr___redArg___closed__20);
v___x_638_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__21));
v___x_639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v___x_636_);
v___x_640_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__22));
v___x_641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_637_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set_uint8(v___x_643_, sizeof(void*)*1, v___x_621_);
return v___x_643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleHeader_repr(lean_object* v_x_646_, lean_object* v_prec_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_instReprModuleHeader_repr___redArg(v_x_646_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleHeader_repr___boxed(lean_object* v_x_649_, lean_object* v_prec_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_instReprModuleHeader_repr(v_x_649_, v_prec_650_);
lean_dec(v_prec_650_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0(size_t v_sz_661_, size_t v_i_662_, lean_object* v_bs_663_){
_start:
{
uint8_t v___x_664_; 
v___x_664_ = lean_usize_dec_lt(v_i_662_, v_sz_661_);
if (v___x_664_ == 0)
{
return v_bs_663_;
}
else
{
lean_object* v_v_665_; lean_object* v___x_666_; lean_object* v_bs_x27_667_; lean_object* v___x_668_; size_t v___x_669_; size_t v___x_670_; lean_object* v___x_671_; 
v_v_665_ = lean_array_uget(v_bs_663_, v_i_662_);
v___x_666_ = lean_unsigned_to_nat(0u);
v_bs_x27_667_ = lean_array_uset(v_bs_663_, v_i_662_, v___x_666_);
v___x_668_ = l_Lean_instToJsonImport_toJson(v_v_665_);
v___x_669_ = ((size_t)1ULL);
v___x_670_ = lean_usize_add(v_i_662_, v___x_669_);
v___x_671_ = lean_array_uset(v_bs_x27_667_, v_i_662_, v___x_668_);
v_i_662_ = v___x_670_;
v_bs_663_ = v___x_671_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0___boxed(lean_object* v_sz_673_, lean_object* v_i_674_, lean_object* v_bs_675_){
_start:
{
size_t v_sz_boxed_676_; size_t v_i_boxed_677_; lean_object* v_res_678_; 
v_sz_boxed_676_ = lean_unbox_usize(v_sz_673_);
lean_dec(v_sz_673_);
v_i_boxed_677_ = lean_unbox_usize(v_i_674_);
lean_dec(v_i_674_);
v_res_678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0(v_sz_boxed_676_, v_i_boxed_677_, v_bs_675_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0(lean_object* v_a_679_){
_start:
{
size_t v_sz_680_; size_t v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v_sz_680_ = lean_array_size(v_a_679_);
v___x_681_ = ((size_t)0ULL);
v___x_682_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0(v_sz_680_, v___x_681_, v_a_679_);
v___x_683_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonModuleHeader_toJson(lean_object* v_x_684_){
_start:
{
lean_object* v_imports_685_; uint8_t v_isModule_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_imports_685_ = lean_ctor_get(v_x_684_, 0);
lean_inc_ref(v_imports_685_);
v_isModule_686_ = lean_ctor_get_uint8(v_x_684_, sizeof(void*)*1);
lean_dec_ref(v_x_684_);
v___x_687_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__0));
v___x_688_ = l_Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0(v_imports_685_);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_687_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = lean_box(0);
v___x_691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_689_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v___x_692_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__5));
v___x_693_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_693_, 0, v_isModule_686_);
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___x_690_);
v___x_696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v___x_690_);
v___x_697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_691_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = ((lean_object*)(l_Lean_instToJsonImport_toJson___closed__0));
v___x_699_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(v___x_697_, v___x_698_);
v___x_700_ = l_Lean_Json_mkObj(v___x_699_);
lean_dec(v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1(size_t v_sz_703_, size_t v_i_704_, lean_object* v_bs_705_){
_start:
{
uint8_t v___x_706_; 
v___x_706_ = lean_usize_dec_lt(v_i_704_, v_sz_703_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; 
v___x_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_707_, 0, v_bs_705_);
return v___x_707_;
}
else
{
lean_object* v_v_708_; lean_object* v___x_709_; 
v_v_708_ = lean_array_uget_borrowed(v_bs_705_, v_i_704_);
lean_inc(v_v_708_);
v___x_709_ = l_Lean_instFromJsonImport_fromJson(v_v_708_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec_ref(v_bs_705_);
v_a_710_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_709_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_709_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
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
lean_object* v_a_718_; lean_object* v___x_719_; lean_object* v_bs_x27_720_; size_t v___x_721_; size_t v___x_722_; lean_object* v___x_723_; 
v_a_718_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_709_, 1);
v___x_719_ = lean_unsigned_to_nat(0u);
v_bs_x27_720_ = lean_array_uset(v_bs_705_, v_i_704_, v___x_719_);
v___x_721_ = ((size_t)1ULL);
v___x_722_ = lean_usize_add(v_i_704_, v___x_721_);
v___x_723_ = lean_array_uset(v_bs_x27_720_, v_i_704_, v_a_718_);
v_i_704_ = v___x_722_;
v_bs_705_ = v___x_723_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_725_, lean_object* v_i_726_, lean_object* v_bs_727_){
_start:
{
size_t v_sz_boxed_728_; size_t v_i_boxed_729_; lean_object* v_res_730_; 
v_sz_boxed_728_ = lean_unbox_usize(v_sz_725_);
lean_dec(v_sz_725_);
v_i_boxed_729_ = lean_unbox_usize(v_i_726_);
lean_dec(v_i_726_);
v_res_730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_728_, v_i_boxed_729_, v_bs_727_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0(lean_object* v_x_733_){
_start:
{
if (lean_obj_tag(v_x_733_) == 4)
{
lean_object* v_elems_734_; size_t v_sz_735_; size_t v___x_736_; lean_object* v___x_737_; 
v_elems_734_ = lean_ctor_get(v_x_733_, 0);
lean_inc_ref(v_elems_734_);
lean_dec_ref_known(v_x_733_, 1);
v_sz_735_ = lean_array_size(v_elems_734_);
v___x_736_ = ((size_t)0ULL);
v___x_737_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1(v_sz_735_, v___x_736_, v_elems_734_);
return v___x_737_;
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_738_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0));
v___x_739_ = lean_unsigned_to_nat(80u);
v___x_740_ = l_Lean_Json_pretty(v_x_733_, v___x_739_);
v___x_741_ = lean_string_append(v___x_738_, v___x_740_);
lean_dec_ref(v___x_740_);
v___x_742_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_743_ = lean_string_append(v___x_741_, v___x_742_);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0(lean_object* v_j_745_, lean_object* v_k_746_){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = l_Lean_Json_getObjValD(v_j_745_, v_k_746_);
v___x_748_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0(v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0___boxed(lean_object* v_j_749_, lean_object* v_k_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0(v_j_749_, v_k_750_);
lean_dec_ref(v_k_750_);
return v_res_751_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__2(void){
_start:
{
uint8_t v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_756_ = 1;
v___x_757_ = ((lean_object*)(l_Lean_instFromJsonModuleHeader_fromJson___closed__1));
v___x_758_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_757_, v___x_756_);
return v___x_758_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__3(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_759_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__4));
v___x_760_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__2, &l_Lean_instFromJsonModuleHeader_fromJson___closed__2_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__2);
v___x_761_ = lean_string_append(v___x_760_, v___x_759_);
return v___x_761_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__5(void){
_start:
{
uint8_t v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_764_ = 1;
v___x_765_ = ((lean_object*)(l_Lean_instFromJsonModuleHeader_fromJson___closed__4));
v___x_766_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_765_, v___x_764_);
return v___x_766_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__6(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_767_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__5, &l_Lean_instFromJsonModuleHeader_fromJson___closed__5_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__5);
v___x_768_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__3, &l_Lean_instFromJsonModuleHeader_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__3);
v___x_769_ = lean_string_append(v___x_768_, v___x_767_);
return v___x_769_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__7(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_770_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_771_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__6, &l_Lean_instFromJsonModuleHeader_fromJson___closed__6_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__6);
v___x_772_ = lean_string_append(v___x_771_, v___x_770_);
return v___x_772_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__9(void){
_start:
{
uint8_t v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_775_ = 1;
v___x_776_ = ((lean_object*)(l_Lean_instFromJsonModuleHeader_fromJson___closed__8));
v___x_777_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_776_, v___x_775_);
return v___x_777_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__10(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_778_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__9, &l_Lean_instFromJsonModuleHeader_fromJson___closed__9_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__9);
v___x_779_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__3, &l_Lean_instFromJsonModuleHeader_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__3);
v___x_780_ = lean_string_append(v___x_779_, v___x_778_);
return v___x_780_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__11(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_781_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_782_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__10, &l_Lean_instFromJsonModuleHeader_fromJson___closed__10_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__10);
v___x_783_ = lean_string_append(v___x_782_, v___x_781_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonModuleHeader_fromJson(lean_object* v_json_784_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__0));
lean_inc(v_json_784_);
v___x_786_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0(v_json_784_, v___x_785_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_796_; 
lean_dec(v_json_784_);
v_a_787_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_796_ == 0)
{
v___x_789_ = v___x_786_;
v_isShared_790_ = v_isSharedCheck_796_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_786_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_796_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_791_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__7, &l_Lean_instFromJsonModuleHeader_fromJson___closed__7_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__7);
v___x_792_ = lean_string_append(v___x_791_, v_a_787_);
lean_dec(v_a_787_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_792_);
v___x_794_ = v___x_789_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v_a_797_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_797_);
lean_dec_ref_known(v___x_786_, 1);
v___x_798_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__5));
v___x_799_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(v_json_784_, v___x_798_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_809_; 
lean_dec(v_a_797_);
v_a_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_809_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_809_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_809_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_804_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__11, &l_Lean_instFromJsonModuleHeader_fromJson___closed__11_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__11);
v___x_805_ = lean_string_append(v___x_804_, v_a_800_);
lean_dec(v_a_800_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_805_);
v___x_807_ = v___x_802_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_819_; 
v_a_810_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_819_ == 0)
{
v___x_812_ = v___x_799_;
v_isShared_813_ = v_isSharedCheck_819_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_799_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_819_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; uint8_t v___x_815_; lean_object* v___x_817_; 
v___x_814_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_814_, 0, v_a_797_);
v___x_815_ = lean_unbox(v_a_810_);
lean_dec(v_a_810_);
lean_ctor_set_uint8(v___x_814_, sizeof(void*)*1, v___x_815_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_814_);
v___x_817_ = v___x_812_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_814_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0(lean_object* v___y_825_){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_826_ = lean_unsigned_to_nat(0u);
v___x_827_ = ((lean_object*)(l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_828_ = l_String_quote(v___y_825_);
v___x_829_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
v___x_830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_827_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = l_Repr_addAppParen(v___x_830_, v___x_826_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_x_832_, lean_object* v_x_833_, lean_object* v_x_834_){
_start:
{
if (lean_obj_tag(v_x_834_) == 0)
{
lean_dec(v_x_832_);
return v_x_833_;
}
else
{
lean_object* v_head_835_; lean_object* v_tail_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_851_; 
v_head_835_ = lean_ctor_get(v_x_834_, 0);
v_tail_836_ = lean_ctor_get(v_x_834_, 1);
v_isSharedCheck_851_ = !lean_is_exclusive(v_x_834_);
if (v_isSharedCheck_851_ == 0)
{
v___x_838_ = v_x_834_;
v_isShared_839_ = v_isSharedCheck_851_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_tail_836_);
lean_inc(v_head_835_);
lean_dec(v_x_834_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_851_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
lean_inc(v_x_832_);
if (v_isShared_839_ == 0)
{
lean_ctor_set_tag(v___x_838_, 5);
lean_ctor_set(v___x_838_, 1, v_x_832_);
lean_ctor_set(v___x_838_, 0, v_x_833_);
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_x_833_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_x_832_);
v___x_841_ = v_reuseFailAlloc_850_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_842_ = lean_unsigned_to_nat(0u);
v___x_843_ = ((lean_object*)(l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_844_ = l_String_quote(v_head_835_);
v___x_845_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
v___x_846_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_843_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = l_Repr_addAppParen(v___x_846_, v___x_842_);
v___x_848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_841_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v_x_833_ = v___x_848_;
v_x_834_ = v_tail_836_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_852_, lean_object* v_x_853_, lean_object* v_x_854_){
_start:
{
if (lean_obj_tag(v_x_854_) == 0)
{
lean_dec(v_x_852_);
return v_x_853_;
}
else
{
lean_object* v_head_855_; lean_object* v_tail_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_871_; 
v_head_855_ = lean_ctor_get(v_x_854_, 0);
v_tail_856_ = lean_ctor_get(v_x_854_, 1);
v_isSharedCheck_871_ = !lean_is_exclusive(v_x_854_);
if (v_isSharedCheck_871_ == 0)
{
v___x_858_ = v_x_854_;
v_isShared_859_ = v_isSharedCheck_871_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_tail_856_);
lean_inc(v_head_855_);
lean_dec(v_x_854_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_871_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
lean_inc(v_x_852_);
if (v_isShared_859_ == 0)
{
lean_ctor_set_tag(v___x_858_, 5);
lean_ctor_set(v___x_858_, 1, v_x_852_);
lean_ctor_set(v___x_858_, 0, v_x_853_);
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_x_853_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_x_852_);
v___x_861_ = v_reuseFailAlloc_870_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_862_ = lean_unsigned_to_nat(0u);
v___x_863_ = ((lean_object*)(l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_864_ = l_String_quote(v_head_855_);
v___x_865_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
v___x_866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_863_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = l_Repr_addAppParen(v___x_866_, v___x_862_);
v___x_868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_861_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2_spec__4(v_x_852_, v___x_868_, v_tail_856_);
return v___x_869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1(lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
if (lean_obj_tag(v_x_872_) == 0)
{
lean_object* v___x_874_; 
lean_dec(v_x_873_);
v___x_874_ = lean_box(0);
return v___x_874_;
}
else
{
lean_object* v_tail_875_; 
v_tail_875_ = lean_ctor_get(v_x_872_, 1);
if (lean_obj_tag(v_tail_875_) == 0)
{
lean_object* v_head_876_; lean_object* v___x_877_; 
lean_dec(v_x_873_);
v_head_876_ = lean_ctor_get(v_x_872_, 0);
lean_inc(v_head_876_);
lean_dec_ref_known(v_x_872_, 2);
v___x_877_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0(v_head_876_);
return v___x_877_;
}
else
{
lean_object* v_head_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
lean_inc(v_tail_875_);
v_head_878_ = lean_ctor_get(v_x_872_, 0);
lean_inc(v_head_878_);
lean_dec_ref_known(v_x_872_, 2);
v___x_879_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0(v_head_878_);
v___x_880_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2(v_x_873_, v___x_879_, v_tail_875_);
return v___x_880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0(lean_object* v_xs_881_){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_882_ = lean_array_get_size(v_xs_881_);
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = lean_nat_dec_eq(v___x_882_, v___x_883_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_885_ = lean_array_to_list(v_xs_881_);
v___x_886_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_887_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1(v___x_885_, v___x_886_);
v___x_888_ = lean_obj_once(&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4);
v___x_889_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5));
v___x_890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
lean_ctor_set(v___x_890_, 1, v___x_887_);
v___x_891_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6));
v___x_892_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_890_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_888_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = l_Std_Format_fill(v___x_893_);
return v___x_894_;
}
else
{
lean_object* v___x_895_; 
lean_dec_ref(v_xs_881_);
v___x_895_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8));
return v___x_895_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__1_spec__3(lean_object* v_x_896_, lean_object* v_x_897_, lean_object* v_x_898_){
_start:
{
if (lean_obj_tag(v_x_898_) == 0)
{
lean_dec(v_x_896_);
return v_x_897_;
}
else
{
lean_object* v_head_899_; lean_object* v_tail_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_910_; 
v_head_899_ = lean_ctor_get(v_x_898_, 0);
v_tail_900_ = lean_ctor_get(v_x_898_, 1);
v_isSharedCheck_910_ = !lean_is_exclusive(v_x_898_);
if (v_isSharedCheck_910_ == 0)
{
v___x_902_ = v_x_898_;
v_isShared_903_ = v_isSharedCheck_910_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_tail_900_);
lean_inc(v_head_899_);
lean_dec(v_x_898_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_910_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
lean_inc(v_x_896_);
if (v_isShared_903_ == 0)
{
lean_ctor_set_tag(v___x_902_, 5);
lean_ctor_set(v___x_902_, 1, v_x_896_);
lean_ctor_set(v___x_902_, 0, v_x_897_);
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_x_897_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_x_896_);
v___x_905_ = v_reuseFailAlloc_909_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = l_Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0(v_head_899_);
v___x_907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_905_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v_x_897_ = v___x_907_;
v_x_898_ = v_tail_900_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__1(lean_object* v_x_911_, lean_object* v_x_912_){
_start:
{
if (lean_obj_tag(v_x_911_) == 0)
{
lean_object* v___x_913_; 
lean_dec(v_x_912_);
v___x_913_ = lean_box(0);
return v___x_913_;
}
else
{
lean_object* v_tail_914_; 
v_tail_914_ = lean_ctor_get(v_x_911_, 1);
if (lean_obj_tag(v_tail_914_) == 0)
{
lean_object* v_head_915_; lean_object* v___x_916_; 
lean_dec(v_x_912_);
v_head_915_ = lean_ctor_get(v_x_911_, 0);
lean_inc(v_head_915_);
lean_dec_ref_known(v_x_911_, 2);
v___x_916_ = l_Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0(v_head_915_);
return v___x_916_;
}
else
{
lean_object* v_head_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
lean_inc(v_tail_914_);
v_head_917_ = lean_ctor_get(v_x_911_, 0);
lean_inc(v_head_917_);
lean_dec_ref_known(v_x_911_, 2);
v___x_918_ = l_Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0(v_head_917_);
v___x_919_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__1_spec__3(v_x_912_, v___x_918_, v_tail_914_);
return v___x_919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0(lean_object* v_xs_920_){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_921_ = lean_array_get_size(v_xs_920_);
v___x_922_ = lean_unsigned_to_nat(0u);
v___x_923_ = lean_nat_dec_eq(v___x_921_, v___x_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_924_ = lean_array_to_list(v_xs_920_);
v___x_925_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_926_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__1(v___x_924_, v___x_925_);
v___x_927_ = lean_obj_once(&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4);
v___x_928_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5));
v___x_929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v___x_926_);
v___x_930_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6));
v___x_931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_927_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = l_Std_Format_fill(v___x_932_);
return v___x_933_;
}
else
{
lean_object* v___x_934_; 
lean_dec_ref(v_xs_920_);
v___x_934_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8));
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprImportArtifacts_repr___redArg(lean_object* v_x_944_){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_945_ = ((lean_object*)(l_Lean_instReprImportArtifacts_repr___redArg___closed__3));
v___x_946_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__7, &l_Lean_instReprModuleHeader_repr___redArg___closed__7_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__7);
v___x_947_ = l_Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0(v_x_944_);
v___x_948_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_946_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = 0;
v___x_950_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_950_, 0, v___x_948_);
lean_ctor_set_uint8(v___x_950_, sizeof(void*)*1, v___x_949_);
v___x_951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_945_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__20, &l_Lean_instReprImport_repr___redArg___closed__20_once, _init_l_Lean_instReprImport_repr___redArg___closed__20);
v___x_953_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__21));
v___x_954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
lean_ctor_set(v___x_954_, 1, v___x_951_);
v___x_955_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__22));
v___x_956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_954_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_952_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_958_, 0, v___x_957_);
lean_ctor_set_uint8(v___x_958_, sizeof(void*)*1, v___x_949_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprImportArtifacts_repr(lean_object* v_x_959_, lean_object* v_prec_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_instReprImportArtifacts_repr___redArg(v_x_959_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprImportArtifacts_repr___boxed(lean_object* v_x_962_, lean_object* v_prec_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_instReprImportArtifacts_repr(v_x_962_, v_prec_963_);
lean_dec(v_prec_963_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonImportArtifacts___lam__0(lean_object* v___x_971_, lean_object* v_x_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Lean_Array_toJson___redArg(v___x_971_, v_x_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonImportArtifacts___lam__0(lean_object* v___x_980_, lean_object* v_x_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_Array_fromJson_x3f___redArg(v___x_980_, v_x_981_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_982_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_982_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
v_a_991_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_982_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_982_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_olean_x3f(lean_object* v_arts_1005_){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = lean_array_get_size(v_arts_1005_);
v___x_1008_ = lean_nat_dec_lt(v___x_1006_, v___x_1007_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_box(0);
return v___x_1009_;
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1010_ = lean_array_fget_borrowed(v_arts_1005_, v___x_1006_);
v___x_1011_ = lean_array_get_size(v___x_1010_);
v___x_1012_ = lean_nat_dec_lt(v___x_1006_, v___x_1011_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_box(0);
return v___x_1013_;
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = lean_array_fget_borrowed(v___x_1010_, v___x_1006_);
lean_inc(v___x_1014_);
v___x_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
return v___x_1015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_olean_x3f___boxed(lean_object* v_arts_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_ImportArtifacts_olean_x3f(v_arts_1016_);
lean_dec_ref(v_arts_1016_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanServer_x3f(lean_object* v_arts_1018_){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; uint8_t v___x_1021_; 
v___x_1019_ = lean_unsigned_to_nat(0u);
v___x_1020_ = lean_array_get_size(v_arts_1018_);
v___x_1021_ = lean_nat_dec_lt(v___x_1019_, v___x_1020_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_box(0);
return v___x_1022_;
}
else
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v___x_1023_ = lean_array_fget_borrowed(v_arts_1018_, v___x_1019_);
v___x_1024_ = lean_unsigned_to_nat(1u);
v___x_1025_ = lean_array_get_size(v___x_1023_);
v___x_1026_ = lean_nat_dec_lt(v___x_1024_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_box(0);
return v___x_1027_;
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = lean_array_fget_borrowed(v___x_1023_, v___x_1024_);
lean_inc(v___x_1028_);
v___x_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
return v___x_1029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanServer_x3f___boxed(lean_object* v_arts_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_ImportArtifacts_oleanServer_x3f(v_arts_1030_);
lean_dec_ref(v_arts_1030_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanPrivate_x3f(lean_object* v_arts_1032_){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = lean_array_get_size(v_arts_1032_);
v___x_1035_ = lean_nat_dec_lt(v___x_1033_, v___x_1034_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_box(0);
return v___x_1036_;
}
else
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1037_ = lean_array_fget_borrowed(v_arts_1032_, v___x_1033_);
v___x_1038_ = lean_unsigned_to_nat(2u);
v___x_1039_ = lean_array_get_size(v___x_1037_);
v___x_1040_ = lean_nat_dec_lt(v___x_1038_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_box(0);
return v___x_1041_;
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_array_fget_borrowed(v___x_1037_, v___x_1038_);
lean_inc(v___x_1042_);
v___x_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
return v___x_1043_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanPrivate_x3f___boxed(lean_object* v_arts_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_ImportArtifacts_oleanPrivate_x3f(v_arts_1044_);
lean_dec_ref(v_arts_1044_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_irSig_x3f(lean_object* v_arts_1046_){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1047_ = lean_unsigned_to_nat(1u);
v___x_1048_ = lean_array_get_size(v_arts_1046_);
v___x_1049_ = lean_nat_dec_lt(v___x_1047_, v___x_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_box(0);
return v___x_1050_;
}
else
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1051_ = lean_array_fget_borrowed(v_arts_1046_, v___x_1047_);
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = lean_array_get_size(v___x_1051_);
v___x_1054_ = lean_nat_dec_lt(v___x_1052_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_box(0);
return v___x_1055_;
}
else
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_array_fget_borrowed(v___x_1051_, v___x_1052_);
lean_inc(v___x_1056_);
v___x_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_irSig_x3f___boxed(lean_object* v_arts_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_ImportArtifacts_irSig_x3f(v_arts_1058_);
lean_dec_ref(v_arts_1058_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_ir_x3f(lean_object* v_arts_1060_){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1061_ = lean_unsigned_to_nat(1u);
v___x_1062_ = lean_array_get_size(v_arts_1060_);
v___x_1063_ = lean_nat_dec_lt(v___x_1061_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_box(0);
return v___x_1064_;
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1065_ = lean_array_fget_borrowed(v_arts_1060_, v___x_1061_);
v___x_1066_ = lean_array_get_size(v___x_1065_);
v___x_1067_ = lean_nat_dec_lt(v___x_1061_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_box(0);
return v___x_1068_;
}
else
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_array_fget_borrowed(v___x_1065_, v___x_1061_);
lean_inc(v___x_1069_);
v___x_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
return v___x_1070_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_ir_x3f___boxed(lean_object* v_arts_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_ImportArtifacts_ir_x3f(v_arts_1071_);
lean_dec_ref(v_arts_1071_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanParts(uint8_t v_inServer_1075_, lean_object* v_arts_1076_){
_start:
{
lean_object* v_fnames_1078_; lean_object* v_fnames_1082_; lean_object* v___x_1083_; 
v_fnames_1082_ = ((lean_object*)(l_Lean_ImportArtifacts_oleanParts___closed__0));
v___x_1083_ = l_Lean_ImportArtifacts_olean_x3f(v_arts_1076_);
if (lean_obj_tag(v___x_1083_) == 1)
{
lean_object* v_val_1084_; lean_object* v_fnames_1085_; lean_object* v___x_1086_; 
v_val_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_val_1084_);
lean_dec_ref_known(v___x_1083_, 1);
v_fnames_1085_ = lean_array_push(v_fnames_1082_, v_val_1084_);
v___x_1086_ = l_Lean_ImportArtifacts_oleanServer_x3f(v_arts_1076_);
if (lean_obj_tag(v___x_1086_) == 1)
{
lean_object* v_val_1087_; 
v_val_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_val_1087_);
lean_dec_ref_known(v___x_1086_, 1);
if (v_inServer_1075_ == 0)
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_ImportArtifacts_oleanPrivate_x3f(v_arts_1076_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_dec(v_val_1087_);
v_fnames_1078_ = v_fnames_1085_;
goto v___jp_1077_;
}
else
{
lean_dec_ref_known(v___x_1090_, 1);
goto v___jp_1088_;
}
}
else
{
goto v___jp_1088_;
}
v___jp_1088_:
{
lean_object* v_fnames_1089_; 
v_fnames_1089_ = lean_array_push(v_fnames_1085_, v_val_1087_);
v_fnames_1078_ = v_fnames_1089_;
goto v___jp_1077_;
}
}
else
{
lean_dec(v___x_1086_);
return v_fnames_1085_;
}
}
else
{
lean_dec(v___x_1083_);
return v_fnames_1082_;
}
v___jp_1077_:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_ImportArtifacts_oleanPrivate_x3f(v_arts_1076_);
if (lean_obj_tag(v___x_1079_) == 1)
{
lean_object* v_val_1080_; lean_object* v_fnames_1081_; 
v_val_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_val_1080_);
lean_dec_ref_known(v___x_1079_, 1);
v_fnames_1081_ = lean_array_push(v_fnames_1078_, v_val_1080_);
return v_fnames_1081_;
}
else
{
lean_dec(v___x_1079_);
return v_fnames_1078_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanParts___boxed(lean_object* v_inServer_1091_, lean_object* v_arts_1092_){
_start:
{
uint8_t v_inServer_boxed_1093_; lean_object* v_res_1094_; 
v_inServer_boxed_1093_ = lean_unbox(v_inServer_1091_);
v_res_1094_ = l_Lean_ImportArtifacts_oleanParts(v_inServer_boxed_1093_, v_arts_1092_);
lean_dec_ref(v_arts_1092_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_irParts(lean_object* v_arts_1095_){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; uint8_t v___x_1098_; 
v___x_1096_ = lean_unsigned_to_nat(1u);
v___x_1097_ = lean_array_get_size(v_arts_1095_);
v___x_1098_ = lean_nat_dec_lt(v___x_1096_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; 
v___x_1099_ = ((lean_object*)(l_Lean_ImportArtifacts_oleanParts___closed__0));
return v___x_1099_;
}
else
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_array_fget_borrowed(v_arts_1095_, v___x_1096_);
lean_inc(v___x_1100_);
return v___x_1100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_irParts___boxed(lean_object* v_arts_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_ImportArtifacts_irParts(v_arts_1101_);
lean_dec_ref(v_arts_1101_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(lean_object* v_x_1109_, lean_object* v_x_1110_){
_start:
{
if (lean_obj_tag(v_x_1109_) == 0)
{
lean_object* v___x_1111_; 
v___x_1111_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__1));
return v___x_1111_;
}
else
{
lean_object* v_val_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1127_; 
v_val_1112_ = lean_ctor_get(v_x_1109_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_x_1109_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1114_ = v_x_1109_;
v_isShared_1115_ = v_isSharedCheck_1127_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_val_1112_);
lean_dec(v_x_1109_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1127_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1121_; 
v___x_1116_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__3));
v___x_1117_ = lean_unsigned_to_nat(1024u);
v___x_1118_ = ((lean_object*)(l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_1119_ = l_String_quote(v_val_1112_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set_tag(v___x_1114_, 3);
lean_ctor_set(v___x_1114_, 0, v___x_1119_);
v___x_1121_ = v___x_1114_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1118_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = l_Repr_addAppParen(v___x_1122_, v___x_1117_);
v___x_1124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1116_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = l_Repr_addAppParen(v___x_1124_, v_x_1110_);
return v___x_1125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___boxed(lean_object* v_x_1128_, lean_object* v_x_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_x_1128_, v_x_1129_);
lean_dec(v_x_1129_);
return v_res_1130_;
}
}
static lean_object* _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_unsigned_to_nat(9u);
v___x_1141_ = lean_nat_to_int(v___x_1140_);
return v___x_1141_;
}
}
static lean_object* _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = lean_unsigned_to_nat(16u);
v___x_1149_ = lean_nat_to_int(v___x_1148_);
return v___x_1149_;
}
}
static lean_object* _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_unsigned_to_nat(17u);
v___x_1154_ = lean_nat_to_int(v___x_1153_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_unsigned_to_nat(7u);
v___x_1165_ = lean_nat_to_int(v___x_1164_);
return v___x_1165_;
}
}
static lean_object* _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = lean_unsigned_to_nat(6u);
v___x_1170_ = lean_nat_to_int(v___x_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleArtifacts_repr___redArg(lean_object* v_x_1174_){
_start:
{
lean_object* v_lean_x3f_1175_; lean_object* v_olean_x3f_1176_; lean_object* v_oleanServer_x3f_1177_; lean_object* v_oleanPrivate_x3f_1178_; lean_object* v_ilean_x3f_1179_; lean_object* v_irSig_x3f_1180_; lean_object* v_ir_x3f_1181_; lean_object* v_c_x3f_1182_; lean_object* v_bc_x3f_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; uint8_t v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v_lean_x3f_1175_ = lean_ctor_get(v_x_1174_, 0);
lean_inc(v_lean_x3f_1175_);
v_olean_x3f_1176_ = lean_ctor_get(v_x_1174_, 1);
lean_inc(v_olean_x3f_1176_);
v_oleanServer_x3f_1177_ = lean_ctor_get(v_x_1174_, 2);
lean_inc(v_oleanServer_x3f_1177_);
v_oleanPrivate_x3f_1178_ = lean_ctor_get(v_x_1174_, 3);
lean_inc(v_oleanPrivate_x3f_1178_);
v_ilean_x3f_1179_ = lean_ctor_get(v_x_1174_, 4);
lean_inc(v_ilean_x3f_1179_);
v_irSig_x3f_1180_ = lean_ctor_get(v_x_1174_, 5);
lean_inc(v_irSig_x3f_1180_);
v_ir_x3f_1181_ = lean_ctor_get(v_x_1174_, 6);
lean_inc(v_ir_x3f_1181_);
v_c_x3f_1182_ = lean_ctor_get(v_x_1174_, 7);
lean_inc(v_c_x3f_1182_);
v_bc_x3f_1183_ = lean_ctor_get(v_x_1174_, 8);
lean_inc(v_bc_x3f_1183_);
lean_dec_ref(v_x_1174_);
v___x_1184_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__5));
v___x_1185_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__3));
v___x_1186_ = lean_obj_once(&l_Lean_instReprModuleArtifacts_repr___redArg___closed__4, &l_Lean_instReprModuleArtifacts_repr___redArg___closed__4_once, _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__4);
v___x_1187_ = lean_unsigned_to_nat(0u);
v___x_1188_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_lean_x3f_1175_, v___x_1187_);
v___x_1189_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1186_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = 0;
v___x_1191_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set_uint8(v___x_1191_, sizeof(void*)*1, v___x_1190_);
v___x_1192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1185_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__9));
v___x_1194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1192_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___x_1195_ = lean_box(1);
v___x_1196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1194_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
v___x_1197_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__6));
v___x_1198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1196_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
lean_ctor_set(v___x_1199_, 1, v___x_1184_);
v___x_1200_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__7, &l_Lean_instReprImport_repr___redArg___closed__7_once, _init_l_Lean_instReprImport_repr___redArg___closed__7);
v___x_1201_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_olean_x3f_1176_, v___x_1187_);
v___x_1202_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1200_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
lean_ctor_set_uint8(v___x_1203_, sizeof(void*)*1, v___x_1190_);
v___x_1204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1199_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
v___x_1205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
lean_ctor_set(v___x_1205_, 1, v___x_1193_);
v___x_1206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set(v___x_1206_, 1, v___x_1195_);
v___x_1207_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__8));
v___x_1208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1206_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v___x_1209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___x_1184_);
v___x_1210_ = lean_obj_once(&l_Lean_instReprModuleArtifacts_repr___redArg___closed__9, &l_Lean_instReprModuleArtifacts_repr___redArg___closed__9_once, _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__9);
v___x_1211_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_oleanServer_x3f_1177_, v___x_1187_);
v___x_1212_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1210_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set_uint8(v___x_1213_, sizeof(void*)*1, v___x_1190_);
v___x_1214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1209_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
v___x_1215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
lean_ctor_set(v___x_1215_, 1, v___x_1193_);
v___x_1216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
lean_ctor_set(v___x_1216_, 1, v___x_1195_);
v___x_1217_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__11));
v___x_1218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1216_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
lean_ctor_set(v___x_1219_, 1, v___x_1184_);
v___x_1220_ = lean_obj_once(&l_Lean_instReprModuleArtifacts_repr___redArg___closed__12, &l_Lean_instReprModuleArtifacts_repr___redArg___closed__12_once, _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__12);
v___x_1221_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_oleanPrivate_x3f_1178_, v___x_1187_);
v___x_1222_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1220_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v___x_1223_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
lean_ctor_set_uint8(v___x_1223_, sizeof(void*)*1, v___x_1190_);
v___x_1224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1219_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set(v___x_1225_, 1, v___x_1193_);
v___x_1226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v___x_1195_);
v___x_1227_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__14));
v___x_1228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1226_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
lean_ctor_set(v___x_1229_, 1, v___x_1184_);
v___x_1230_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_ilean_x3f_1179_, v___x_1187_);
v___x_1231_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1200_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
v___x_1232_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
lean_ctor_set_uint8(v___x_1232_, sizeof(void*)*1, v___x_1190_);
v___x_1233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1229_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
lean_ctor_set(v___x_1234_, 1, v___x_1193_);
v___x_1235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
lean_ctor_set(v___x_1235_, 1, v___x_1195_);
v___x_1236_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__16));
v___x_1237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1235_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
lean_ctor_set(v___x_1238_, 1, v___x_1184_);
v___x_1239_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_irSig_x3f_1180_, v___x_1187_);
v___x_1240_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1200_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
v___x_1241_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
lean_ctor_set_uint8(v___x_1241_, sizeof(void*)*1, v___x_1190_);
v___x_1242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1238_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
lean_ctor_set(v___x_1243_, 1, v___x_1193_);
v___x_1244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
lean_ctor_set(v___x_1244_, 1, v___x_1195_);
v___x_1245_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__18));
v___x_1246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1244_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
lean_ctor_set(v___x_1247_, 1, v___x_1184_);
v___x_1248_ = lean_obj_once(&l_Lean_instReprModuleArtifacts_repr___redArg___closed__19, &l_Lean_instReprModuleArtifacts_repr___redArg___closed__19_once, _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__19);
v___x_1249_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_ir_x3f_1181_, v___x_1187_);
v___x_1250_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1248_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
lean_ctor_set_uint8(v___x_1251_, sizeof(void*)*1, v___x_1190_);
v___x_1252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1247_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
lean_ctor_set(v___x_1253_, 1, v___x_1193_);
v___x_1254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
lean_ctor_set(v___x_1254_, 1, v___x_1195_);
v___x_1255_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__21));
v___x_1256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1254_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
lean_ctor_set(v___x_1257_, 1, v___x_1184_);
v___x_1258_ = lean_obj_once(&l_Lean_instReprModuleArtifacts_repr___redArg___closed__22, &l_Lean_instReprModuleArtifacts_repr___redArg___closed__22_once, _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__22);
v___x_1259_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_c_x3f_1182_, v___x_1187_);
v___x_1260_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1258_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
lean_ctor_set_uint8(v___x_1261_, sizeof(void*)*1, v___x_1190_);
v___x_1262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1257_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
lean_ctor_set(v___x_1263_, 1, v___x_1193_);
v___x_1264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
lean_ctor_set(v___x_1264_, 1, v___x_1195_);
v___x_1265_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__24));
v___x_1266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1264_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
lean_ctor_set(v___x_1267_, 1, v___x_1184_);
v___x_1268_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_bc_x3f_1183_, v___x_1187_);
v___x_1269_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1248_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
v___x_1270_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
lean_ctor_set_uint8(v___x_1270_, sizeof(void*)*1, v___x_1190_);
v___x_1271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1267_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v___x_1272_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__20, &l_Lean_instReprImport_repr___redArg___closed__20_once, _init_l_Lean_instReprImport_repr___redArg___closed__20);
v___x_1273_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__21));
v___x_1274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
lean_ctor_set(v___x_1274_, 1, v___x_1271_);
v___x_1275_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__22));
v___x_1276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1274_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v___x_1277_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1272_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
v___x_1278_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
lean_ctor_set_uint8(v___x_1278_, sizeof(void*)*1, v___x_1190_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleArtifacts_repr(lean_object* v_x_1279_, lean_object* v_prec_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_instReprModuleArtifacts_repr___redArg(v_x_1279_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleArtifacts_repr___boxed(lean_object* v_x_1282_, lean_object* v_prec_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_instReprModuleArtifacts_repr(v_x_1282_, v_prec_1283_);
lean_dec(v_prec_1283_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(lean_object* v_k_1291_, lean_object* v_x_1292_){
_start:
{
if (lean_obj_tag(v_x_1292_) == 0)
{
lean_object* v___x_1293_; 
lean_dec_ref(v_k_1291_);
v___x_1293_ = lean_box(0);
return v___x_1293_;
}
else
{
lean_object* v_val_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1304_; 
v_val_1294_ = lean_ctor_get(v_x_1292_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_x_1292_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1296_ = v_x_1292_;
v_isShared_1297_ = v_isSharedCheck_1304_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_val_1294_);
lean_dec(v_x_1292_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1304_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
lean_ctor_set_tag(v___x_1296_, 3);
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_val_1294_);
v___x_1299_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v_k_1291_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
v___x_1301_ = lean_box(0);
v___x_1302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1300_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
return v___x_1302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonModuleArtifacts_toJson(lean_object* v_x_1314_){
_start:
{
lean_object* v_lean_x3f_1315_; lean_object* v_olean_x3f_1316_; lean_object* v_oleanServer_x3f_1317_; lean_object* v_oleanPrivate_x3f_1318_; lean_object* v_ilean_x3f_1319_; lean_object* v_irSig_x3f_1320_; lean_object* v_ir_x3f_1321_; lean_object* v_c_x3f_1322_; lean_object* v_bc_x3f_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v_lean_x3f_1315_ = lean_ctor_get(v_x_1314_, 0);
lean_inc(v_lean_x3f_1315_);
v_olean_x3f_1316_ = lean_ctor_get(v_x_1314_, 1);
lean_inc(v_olean_x3f_1316_);
v_oleanServer_x3f_1317_ = lean_ctor_get(v_x_1314_, 2);
lean_inc(v_oleanServer_x3f_1317_);
v_oleanPrivate_x3f_1318_ = lean_ctor_get(v_x_1314_, 3);
lean_inc(v_oleanPrivate_x3f_1318_);
v_ilean_x3f_1319_ = lean_ctor_get(v_x_1314_, 4);
lean_inc(v_ilean_x3f_1319_);
v_irSig_x3f_1320_ = lean_ctor_get(v_x_1314_, 5);
lean_inc(v_irSig_x3f_1320_);
v_ir_x3f_1321_ = lean_ctor_get(v_x_1314_, 6);
lean_inc(v_ir_x3f_1321_);
v_c_x3f_1322_ = lean_ctor_get(v_x_1314_, 7);
lean_inc(v_c_x3f_1322_);
v_bc_x3f_1323_ = lean_ctor_get(v_x_1314_, 8);
lean_inc(v_bc_x3f_1323_);
lean_dec_ref(v_x_1314_);
v___x_1324_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__0));
v___x_1325_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1324_, v_lean_x3f_1315_);
v___x_1326_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__1));
v___x_1327_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1326_, v_olean_x3f_1316_);
v___x_1328_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__2));
v___x_1329_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1328_, v_oleanServer_x3f_1317_);
v___x_1330_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__3));
v___x_1331_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1330_, v_oleanPrivate_x3f_1318_);
v___x_1332_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__4));
v___x_1333_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1332_, v_ilean_x3f_1319_);
v___x_1334_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__5));
v___x_1335_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1334_, v_irSig_x3f_1320_);
v___x_1336_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__6));
v___x_1337_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1336_, v_ir_x3f_1321_);
v___x_1338_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__7));
v___x_1339_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1338_, v_c_x3f_1322_);
v___x_1340_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__8));
v___x_1341_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1340_, v_bc_x3f_1323_);
v___x_1342_ = lean_box(0);
v___x_1343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1341_);
lean_ctor_set(v___x_1343_, 1, v___x_1342_);
v___x_1344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1339_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
v___x_1345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1337_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
v___x_1346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1335_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___x_1347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1333_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
v___x_1348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1331_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1329_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
v___x_1350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1327_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
v___x_1351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1325_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
v___x_1352_ = ((lean_object*)(l_Lean_instToJsonImport_toJson___closed__0));
v___x_1353_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(v___x_1351_, v___x_1352_);
v___x_1354_ = l_Lean_Json_mkObj(v___x_1353_);
lean_dec(v___x_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0(lean_object* v_x_1359_){
_start:
{
if (lean_obj_tag(v_x_1359_) == 0)
{
lean_object* v___x_1360_; 
v___x_1360_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0___closed__0));
return v___x_1360_;
}
else
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_Json_getStr_x3f(v_x_1359_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1378_; 
v_a_1370_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1372_ = v___x_1361_;
v_isShared_1373_ = v_isSharedCheck_1378_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1361_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1378_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1374_, 0, v_a_1370_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1374_);
v___x_1376_ = v___x_1372_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(lean_object* v_j_1379_, lean_object* v_k_1380_){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = l_Lean_Json_getObjValD(v_j_1379_, v_k_1380_);
v___x_1382_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0(v___x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0___boxed(lean_object* v_j_1383_, lean_object* v_k_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_j_1383_, v_k_1384_);
lean_dec_ref(v_k_1384_);
return v_res_1385_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = 1;
v___x_1391_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__1));
v___x_1392_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1391_, v___x_1390_);
return v___x_1392_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1393_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__4));
v___x_1394_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2);
v___x_1395_ = lean_string_append(v___x_1394_, v___x_1393_);
return v___x_1395_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1398_ = 1;
v___x_1399_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__4));
v___x_1400_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1399_, v___x_1398_);
return v___x_1400_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1401_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5);
v___x_1402_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1403_ = lean_string_append(v___x_1402_, v___x_1401_);
return v___x_1403_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1404_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1405_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6);
v___x_1406_ = lean_string_append(v___x_1405_, v___x_1404_);
return v___x_1406_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1409_ = 1;
v___x_1410_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__8));
v___x_1411_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1410_, v___x_1409_);
return v___x_1411_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1412_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9);
v___x_1413_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1414_ = lean_string_append(v___x_1413_, v___x_1412_);
return v___x_1414_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1415_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1416_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10);
v___x_1417_ = lean_string_append(v___x_1416_, v___x_1415_);
return v___x_1417_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13(void){
_start:
{
uint8_t v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1420_ = 1;
v___x_1421_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__12));
v___x_1422_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1421_, v___x_1420_);
return v___x_1422_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1423_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13);
v___x_1424_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1425_ = lean_string_append(v___x_1424_, v___x_1423_);
return v___x_1425_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1426_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1427_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14);
v___x_1428_ = lean_string_append(v___x_1427_, v___x_1426_);
return v___x_1428_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17(void){
_start:
{
uint8_t v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = 1;
v___x_1432_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__16));
v___x_1433_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1432_, v___x_1431_);
return v___x_1433_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1434_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17);
v___x_1435_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1436_ = lean_string_append(v___x_1435_, v___x_1434_);
return v___x_1436_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19(void){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1437_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1438_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18);
v___x_1439_ = lean_string_append(v___x_1438_, v___x_1437_);
return v___x_1439_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1442_ = 1;
v___x_1443_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__20));
v___x_1444_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1443_, v___x_1442_);
return v___x_1444_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1445_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21);
v___x_1446_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1447_ = lean_string_append(v___x_1446_, v___x_1445_);
return v___x_1447_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1448_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1449_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22);
v___x_1450_ = lean_string_append(v___x_1449_, v___x_1448_);
return v___x_1450_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25(void){
_start:
{
uint8_t v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1453_ = 1;
v___x_1454_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__24));
v___x_1455_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1454_, v___x_1453_);
return v___x_1455_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26(void){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1456_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25);
v___x_1457_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1458_ = lean_string_append(v___x_1457_, v___x_1456_);
return v___x_1458_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1459_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1460_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26);
v___x_1461_ = lean_string_append(v___x_1460_, v___x_1459_);
return v___x_1461_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29(void){
_start:
{
uint8_t v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1464_ = 1;
v___x_1465_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__28));
v___x_1466_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1465_, v___x_1464_);
return v___x_1466_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30(void){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1467_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29);
v___x_1468_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1469_ = lean_string_append(v___x_1468_, v___x_1467_);
return v___x_1469_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31(void){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1470_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1471_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30);
v___x_1472_ = lean_string_append(v___x_1471_, v___x_1470_);
return v___x_1472_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33(void){
_start:
{
uint8_t v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1475_ = 1;
v___x_1476_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__32));
v___x_1477_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1476_, v___x_1475_);
return v___x_1477_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34(void){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1478_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33);
v___x_1479_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1480_ = lean_string_append(v___x_1479_, v___x_1478_);
return v___x_1480_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1481_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1482_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34);
v___x_1483_ = lean_string_append(v___x_1482_, v___x_1481_);
return v___x_1483_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__37(void){
_start:
{
uint8_t v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1486_ = 1;
v___x_1487_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__36));
v___x_1488_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1487_, v___x_1486_);
return v___x_1488_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__38(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1489_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__37, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__37_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__37);
v___x_1490_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1491_ = lean_string_append(v___x_1490_, v___x_1489_);
return v___x_1491_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__39(void){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1492_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1493_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__38, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__38_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__38);
v___x_1494_ = lean_string_append(v___x_1493_, v___x_1492_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson(lean_object* v_json_1495_){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__0));
lean_inc(v_json_1495_);
v___x_1497_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1495_, v___x_1496_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v_json_1495_);
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1507_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1507_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1505_; 
v___x_1502_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7);
v___x_1503_ = lean_string_append(v___x_1502_, v_a_1498_);
lean_dec(v_a_1498_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v___x_1503_);
v___x_1505_ = v___x_1500_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v_a_1508_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1508_);
lean_dec_ref_known(v___x_1497_, 1);
v___x_1509_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__1));
lean_inc(v_json_1495_);
v___x_1510_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1495_, v___x_1509_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1520_; 
lean_dec(v_a_1508_);
lean_dec(v_json_1495_);
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1513_ = v___x_1510_;
v_isShared_1514_ = v_isSharedCheck_1520_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1520_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1518_; 
v___x_1515_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11);
v___x_1516_ = lean_string_append(v___x_1515_, v_a_1511_);
lean_dec(v_a_1511_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v___x_1516_);
v___x_1518_ = v___x_1513_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
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
v_a_1521_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1521_);
lean_dec_ref_known(v___x_1510_, 1);
v___x_1522_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__2));
lean_inc(v_json_1495_);
v___x_1523_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1495_, v___x_1522_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1533_; 
lean_dec(v_a_1521_);
lean_dec(v_a_1508_);
lean_dec(v_json_1495_);
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
v___x_1528_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15);
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
lean_object* v_a_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_a_1534_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1523_, 1);
v___x_1535_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__3));
lean_inc(v_json_1495_);
v___x_1536_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1495_, v___x_1535_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1546_; 
lean_dec(v_a_1534_);
lean_dec(v_a_1521_);
lean_dec(v_a_1508_);
lean_dec(v_json_1495_);
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1546_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1546_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1541_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19);
v___x_1542_ = lean_string_append(v___x_1541_, v_a_1537_);
lean_dec(v_a_1537_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1542_);
v___x_1544_ = v___x_1539_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_a_1547_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___x_1536_, 1);
v___x_1548_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__4));
lean_inc(v_json_1495_);
v___x_1549_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1495_, v___x_1548_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1559_; 
lean_dec(v_a_1547_);
lean_dec(v_a_1534_);
lean_dec(v_a_1521_);
lean_dec(v_a_1508_);
lean_dec(v_json_1495_);
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1552_ = v___x_1549_;
v_isShared_1553_ = v_isSharedCheck_1559_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1559_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1557_; 
v___x_1554_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23);
v___x_1555_ = lean_string_append(v___x_1554_, v_a_1550_);
lean_dec(v_a_1550_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1555_);
v___x_1557_ = v___x_1552_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v_a_1560_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1560_);
lean_dec_ref_known(v___x_1549_, 1);
v___x_1561_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__5));
lean_inc(v_json_1495_);
v___x_1562_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1495_, v___x_1561_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1572_; 
lean_dec(v_a_1560_);
lean_dec(v_a_1547_);
lean_dec(v_a_1534_);
lean_dec(v_a_1521_);
lean_dec(v_a_1508_);
lean_dec(v_json_1495_);
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
v___x_1567_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27);
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
lean_object* v_a_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v_a_1573_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v___x_1562_, 1);
v___x_1574_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__6));
lean_inc(v_json_1495_);
v___x_1575_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1495_, v___x_1574_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1585_; 
lean_dec(v_a_1573_);
lean_dec(v_a_1560_);
lean_dec(v_a_1547_);
lean_dec(v_a_1534_);
lean_dec(v_a_1521_);
lean_dec(v_a_1508_);
lean_dec(v_json_1495_);
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1578_ = v___x_1575_;
v_isShared_1579_ = v_isSharedCheck_1585_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1575_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1585_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1580_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31);
v___x_1581_ = lean_string_append(v___x_1580_, v_a_1576_);
lean_dec(v_a_1576_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v___x_1581_);
v___x_1583_ = v___x_1578_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v_a_1586_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___x_1575_, 1);
v___x_1587_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__7));
lean_inc(v_json_1495_);
v___x_1588_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1495_, v___x_1587_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1598_; 
lean_dec(v_a_1586_);
lean_dec(v_a_1573_);
lean_dec(v_a_1560_);
lean_dec(v_a_1547_);
lean_dec(v_a_1534_);
lean_dec(v_a_1521_);
lean_dec(v_a_1508_);
lean_dec(v_json_1495_);
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1591_ = v___x_1588_;
v_isShared_1592_ = v_isSharedCheck_1598_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1598_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1596_; 
v___x_1593_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35);
v___x_1594_ = lean_string_append(v___x_1593_, v_a_1589_);
lean_dec(v_a_1589_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___x_1594_);
v___x_1596_ = v___x_1591_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v_a_1599_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1588_, 1);
v___x_1600_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__8));
v___x_1601_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1495_, v___x_1600_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1611_; 
lean_dec(v_a_1599_);
lean_dec(v_a_1586_);
lean_dec(v_a_1573_);
lean_dec(v_a_1560_);
lean_dec(v_a_1547_);
lean_dec(v_a_1534_);
lean_dec(v_a_1521_);
lean_dec(v_a_1508_);
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1611_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1611_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1606_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__39, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__39_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__39);
v___x_1607_ = lean_string_append(v___x_1606_, v_a_1602_);
lean_dec(v_a_1602_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1607_);
v___x_1609_ = v___x_1604_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1620_; 
v_a_1612_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1614_ = v___x_1601_;
v_isShared_1615_ = v_isSharedCheck_1620_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1601_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1620_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v___x_1618_; 
v___x_1616_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1616_, 0, v_a_1508_);
lean_ctor_set(v___x_1616_, 1, v_a_1521_);
lean_ctor_set(v___x_1616_, 2, v_a_1534_);
lean_ctor_set(v___x_1616_, 3, v_a_1547_);
lean_ctor_set(v___x_1616_, 4, v_a_1560_);
lean_ctor_set(v___x_1616_, 5, v_a_1573_);
lean_ctor_set(v___x_1616_, 6, v_a_1586_);
lean_ctor_set(v___x_1616_, 7, v_a_1599_);
lean_ctor_set(v___x_1616_, 8, v_a_1612_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 0, v___x_1616_);
v___x_1618_ = v___x_1614_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
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
LEAN_EXPORT lean_object* l_Lean_ModuleArtifacts_oleanParts(lean_object* v_arts_1623_){
_start:
{
lean_object* v_olean_x3f_1624_; lean_object* v_oleanServer_x3f_1625_; lean_object* v_oleanPrivate_x3f_1626_; lean_object* v_fnames_1627_; 
v_olean_x3f_1624_ = lean_ctor_get(v_arts_1623_, 1);
lean_inc(v_olean_x3f_1624_);
v_oleanServer_x3f_1625_ = lean_ctor_get(v_arts_1623_, 2);
lean_inc(v_oleanServer_x3f_1625_);
v_oleanPrivate_x3f_1626_ = lean_ctor_get(v_arts_1623_, 3);
lean_inc(v_oleanPrivate_x3f_1626_);
lean_dec_ref(v_arts_1623_);
v_fnames_1627_ = ((lean_object*)(l_Lean_ImportArtifacts_oleanParts___closed__0));
if (lean_obj_tag(v_olean_x3f_1624_) == 1)
{
lean_object* v_val_1628_; lean_object* v_fnames_1629_; 
v_val_1628_ = lean_ctor_get(v_olean_x3f_1624_, 0);
lean_inc(v_val_1628_);
lean_dec_ref_known(v_olean_x3f_1624_, 1);
v_fnames_1629_ = lean_array_push(v_fnames_1627_, v_val_1628_);
if (lean_obj_tag(v_oleanServer_x3f_1625_) == 1)
{
lean_object* v_val_1630_; lean_object* v_fnames_1631_; 
v_val_1630_ = lean_ctor_get(v_oleanServer_x3f_1625_, 0);
lean_inc(v_val_1630_);
lean_dec_ref_known(v_oleanServer_x3f_1625_, 1);
v_fnames_1631_ = lean_array_push(v_fnames_1629_, v_val_1630_);
if (lean_obj_tag(v_oleanPrivate_x3f_1626_) == 1)
{
lean_object* v_val_1632_; lean_object* v_fnames_1633_; 
v_val_1632_ = lean_ctor_get(v_oleanPrivate_x3f_1626_, 0);
lean_inc(v_val_1632_);
lean_dec_ref_known(v_oleanPrivate_x3f_1626_, 1);
v_fnames_1633_ = lean_array_push(v_fnames_1631_, v_val_1632_);
return v_fnames_1633_;
}
else
{
lean_dec(v_oleanPrivate_x3f_1626_);
return v_fnames_1631_;
}
}
else
{
lean_dec(v_oleanPrivate_x3f_1626_);
lean_dec(v_oleanServer_x3f_1625_);
return v_fnames_1629_;
}
}
else
{
lean_dec(v_oleanPrivate_x3f_1626_);
lean_dec(v_oleanServer_x3f_1625_);
lean_dec(v_olean_x3f_1624_);
return v_fnames_1627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleArtifacts_irParts(lean_object* v_arts_1634_){
_start:
{
lean_object* v_irSig_x3f_1635_; lean_object* v_ir_x3f_1636_; lean_object* v_fnames_1637_; 
v_irSig_x3f_1635_ = lean_ctor_get(v_arts_1634_, 5);
lean_inc(v_irSig_x3f_1635_);
v_ir_x3f_1636_ = lean_ctor_get(v_arts_1634_, 6);
lean_inc(v_ir_x3f_1636_);
lean_dec_ref(v_arts_1634_);
v_fnames_1637_ = ((lean_object*)(l_Lean_ImportArtifacts_oleanParts___closed__0));
if (lean_obj_tag(v_irSig_x3f_1635_) == 1)
{
lean_object* v_val_1638_; lean_object* v_fnames_1639_; 
v_val_1638_ = lean_ctor_get(v_irSig_x3f_1635_, 0);
lean_inc(v_val_1638_);
lean_dec_ref_known(v_irSig_x3f_1635_, 1);
v_fnames_1639_ = lean_array_push(v_fnames_1637_, v_val_1638_);
if (lean_obj_tag(v_ir_x3f_1636_) == 1)
{
lean_object* v_val_1640_; lean_object* v_fnames_1641_; 
v_val_1640_ = lean_ctor_get(v_ir_x3f_1636_, 0);
lean_inc(v_val_1640_);
lean_dec_ref_known(v_ir_x3f_1636_, 1);
v_fnames_1641_ = lean_array_push(v_fnames_1639_, v_val_1640_);
return v_fnames_1641_;
}
else
{
lean_dec(v_ir_x3f_1636_);
return v_fnames_1639_;
}
}
else
{
lean_dec(v_ir_x3f_1636_);
lean_dec(v_irSig_x3f_1635_);
return v_fnames_1637_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0(lean_object* v_x_1642_, lean_object* v_x_1643_){
_start:
{
if (lean_obj_tag(v_x_1642_) == 0)
{
lean_object* v___x_1644_; 
v___x_1644_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__1));
return v___x_1644_;
}
else
{
lean_object* v_val_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1656_; 
v_val_1645_ = lean_ctor_get(v_x_1642_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_x_1642_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1647_ = v_x_1642_;
v_isShared_1648_ = v_isSharedCheck_1656_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_val_1645_);
lean_dec(v_x_1642_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1656_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1649_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__3));
v___x_1650_ = l_String_quote(v_val_1645_);
if (v_isShared_1648_ == 0)
{
lean_ctor_set_tag(v___x_1647_, 3);
lean_ctor_set(v___x_1647_, 0, v___x_1650_);
v___x_1652_ = v___x_1647_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1649_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = l_Repr_addAppParen(v___x_1653_, v_x_1643_);
return v___x_1654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0___boxed(lean_object* v_x_1657_, lean_object* v_x_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0(v_x_1657_, v_x_1658_);
lean_dec(v_x_1658_);
return v_res_1659_;
}
}
static lean_object* _init_l_Lean_instReprPlugin_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = lean_unsigned_to_nat(8u);
v___x_1670_ = lean_nat_to_int(v___x_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprPlugin_repr___redArg(lean_object* v_x_1674_){
_start:
{
lean_object* v_path_1675_; lean_object* v_initFn_x3f_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1714_; 
v_path_1675_ = lean_ctor_get(v_x_1674_, 0);
v_initFn_x3f_1676_ = lean_ctor_get(v_x_1674_, 1);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_x_1674_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1678_ = v_x_1674_;
v_isShared_1679_ = v_isSharedCheck_1714_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_initFn_x3f_1676_);
lean_inc(v_path_1675_);
lean_dec(v_x_1674_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1714_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1680_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__5));
v___x_1681_ = ((lean_object*)(l_Lean_instReprPlugin_repr___redArg___closed__3));
v___x_1682_ = lean_obj_once(&l_Lean_instReprPlugin_repr___redArg___closed__4, &l_Lean_instReprPlugin_repr___redArg___closed__4_once, _init_l_Lean_instReprPlugin_repr___redArg___closed__4);
v___x_1683_ = lean_unsigned_to_nat(0u);
v___x_1684_ = ((lean_object*)(l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_1685_ = l_String_quote(v_path_1675_);
v___x_1686_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set_tag(v___x_1678_, 5);
lean_ctor_set(v___x_1678_, 1, v___x_1686_);
lean_ctor_set(v___x_1678_, 0, v___x_1684_);
v___x_1688_ = v___x_1678_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; uint8_t v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1689_ = l_Repr_addAppParen(v___x_1688_, v___x_1683_);
v___x_1690_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1682_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
v___x_1691_ = 0;
v___x_1692_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1692_, 0, v___x_1690_);
lean_ctor_set_uint8(v___x_1692_, sizeof(void*)*1, v___x_1691_);
v___x_1693_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1681_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__9));
v___x_1695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1693_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = lean_box(1);
v___x_1697_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1695_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
v___x_1698_ = ((lean_object*)(l_Lean_instReprPlugin_repr___redArg___closed__6));
v___x_1699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1697_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1699_);
lean_ctor_set(v___x_1700_, 1, v___x_1680_);
v___x_1701_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__4, &l_Lean_instReprModuleHeader_repr___redArg___closed__4_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__4);
v___x_1702_ = l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0(v_initFn_x3f_1676_, v___x_1683_);
v___x_1703_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1701_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1704_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
lean_ctor_set_uint8(v___x_1704_, sizeof(void*)*1, v___x_1691_);
v___x_1705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1700_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1706_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__20, &l_Lean_instReprImport_repr___redArg___closed__20_once, _init_l_Lean_instReprImport_repr___redArg___closed__20);
v___x_1707_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__21));
v___x_1708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
lean_ctor_set(v___x_1708_, 1, v___x_1705_);
v___x_1709_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__22));
v___x_1710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1708_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
v___x_1711_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1706_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
v___x_1712_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1712_, 0, v___x_1711_);
lean_ctor_set_uint8(v___x_1712_, sizeof(void*)*1, v___x_1691_);
return v___x_1712_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprPlugin_repr(lean_object* v_x_1715_, lean_object* v_prec_1716_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Lean_instReprPlugin_repr___redArg(v_x_1715_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprPlugin_repr___boxed(lean_object* v_x_1718_, lean_object* v_prec_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_instReprPlugin_repr(v_x_1718_, v_prec_1719_);
lean_dec(v_prec_1719_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonPlugin_toJson_spec__0(lean_object* v_k_1723_, lean_object* v_x_1724_){
_start:
{
if (lean_obj_tag(v_x_1724_) == 0)
{
lean_object* v___x_1725_; 
lean_dec_ref(v_k_1723_);
v___x_1725_ = lean_box(0);
return v___x_1725_;
}
else
{
lean_object* v_val_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1736_; 
v_val_1726_ = lean_ctor_get(v_x_1724_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_x_1724_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1728_ = v_x_1724_;
v_isShared_1729_ = v_isSharedCheck_1736_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_val_1726_);
lean_dec(v_x_1724_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1736_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
lean_ctor_set_tag(v___x_1728_, 3);
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_val_1726_);
v___x_1731_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1732_, 0, v_k_1723_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
v___x_1733_ = lean_box(0);
v___x_1734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1732_);
lean_ctor_set(v___x_1734_, 1, v___x_1733_);
return v___x_1734_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonPlugin_toJson(lean_object* v_x_1738_){
_start:
{
lean_object* v_path_1739_; lean_object* v_initFn_x3f_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1758_; 
v_path_1739_ = lean_ctor_get(v_x_1738_, 0);
v_initFn_x3f_1740_ = lean_ctor_get(v_x_1738_, 1);
v_isSharedCheck_1758_ = !lean_is_exclusive(v_x_1738_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1742_ = v_x_1738_;
v_isShared_1743_ = v_isSharedCheck_1758_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_initFn_x3f_1740_);
lean_inc(v_path_1739_);
lean_dec(v_x_1738_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1758_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1747_; 
v___x_1744_ = ((lean_object*)(l_Lean_instReprPlugin_repr___redArg___closed__0));
v___x_1745_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_path_1739_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 1, v___x_1745_);
lean_ctor_set(v___x_1742_, 0, v___x_1744_);
v___x_1747_ = v___x_1742_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1744_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1748_ = lean_box(0);
v___x_1749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1747_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
v___x_1750_ = ((lean_object*)(l_Lean_instToJsonPlugin_toJson___closed__0));
v___x_1751_ = l_Lean_Json_opt___at___00Lean_instToJsonPlugin_toJson_spec__0(v___x_1750_, v_initFn_x3f_1740_);
v___x_1752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
lean_ctor_set(v___x_1752_, 1, v___x_1748_);
v___x_1753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1749_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v___x_1754_ = ((lean_object*)(l_Lean_instToJsonImport_toJson___closed__0));
v___x_1755_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(v___x_1753_, v___x_1754_);
v___x_1756_ = l_Lean_Json_mkObj(v___x_1755_);
lean_dec(v___x_1755_);
return v___x_1756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Plugin_ofFilePath(lean_object* v_path_1761_){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = lean_box(0);
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v_path_1761_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__0(lean_object* v_j_1766_, lean_object* v_k_1767_){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = l_Lean_Json_getObjValD(v_j_1766_, v_k_1767_);
v___x_1769_ = l_Lean_Json_getStr_x3f(v___x_1768_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
v_a_1778_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1769_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1769_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__0___boxed(lean_object* v_j_1786_, lean_object* v_k_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__0(v_j_1786_, v_k_1787_);
lean_dec_ref(v_k_1787_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1_spec__1(lean_object* v_x_1789_){
_start:
{
if (lean_obj_tag(v_x_1789_) == 0)
{
lean_object* v___x_1790_; 
v___x_1790_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0___closed__0));
return v___x_1790_;
}
else
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_Json_getStr_x3f(v_x_1789_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1791_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1791_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1808_; 
v_a_1800_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1802_ = v___x_1791_;
v_isShared_1803_ = v_isSharedCheck_1808_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1791_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1808_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1804_, 0, v_a_1800_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1804_);
v___x_1806_ = v___x_1802_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1804_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1(lean_object* v_j_1809_, lean_object* v_k_1810_){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = l_Lean_Json_getObjValD(v_j_1809_, v_k_1810_);
v___x_1812_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1_spec__1(v___x_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1___boxed(lean_object* v_j_1813_, lean_object* v_k_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1(v_j_1813_, v_k_1814_);
lean_dec_ref(v_k_1814_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Plugin_fromJson_x3f(lean_object* v_data_1819_){
_start:
{
switch(lean_obj_tag(v_data_1819_))
{
case 3:
{
lean_object* v_s_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1828_; 
v_s_1820_ = lean_ctor_get(v_data_1819_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_data_1819_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1822_ = v_data_1819_;
v_isShared_1823_ = v_isSharedCheck_1828_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_s_1820_);
lean_dec(v_data_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1828_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1824_ = l_Lean_Plugin_ofFilePath(v_s_1820_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set_tag(v___x_1822_, 1);
lean_ctor_set(v___x_1822_, 0, v___x_1824_);
v___x_1826_ = v___x_1822_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
case 5:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = ((lean_object*)(l_Lean_instReprPlugin_repr___redArg___closed__0));
lean_inc_ref(v_data_1819_);
v___x_1830_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__0(v_data_1819_, v___x_1829_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
lean_dec_ref_known(v_data_1819_, 1);
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1830_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1830_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v_a_1839_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1839_);
lean_dec_ref_known(v___x_1830_, 1);
v___x_1840_ = ((lean_object*)(l_Lean_instToJsonPlugin_toJson___closed__0));
v___x_1841_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1(v_data_1819_, v___x_1840_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
lean_dec(v_a_1839_);
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1841_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1858_; 
v_a_1850_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1852_ = v___x_1841_;
v_isShared_1853_ = v_isSharedCheck_1858_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1841_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1858_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1854_, 0, v_a_1839_);
lean_ctor_set(v___x_1854_, 1, v_a_1850_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v___x_1854_);
v___x_1856_ = v___x_1852_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
default: 
{
lean_object* v___x_1859_; 
lean_dec(v_data_1819_);
v___x_1859_ = ((lean_object*)(l_Lean_Plugin_fromJson_x3f___closed__1));
return v___x_1859_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2_spec__3_spec__5(lean_object* v_x_1862_, lean_object* v_x_1863_, lean_object* v_x_1864_){
_start:
{
if (lean_obj_tag(v_x_1864_) == 0)
{
lean_dec(v_x_1862_);
return v_x_1863_;
}
else
{
lean_object* v_head_1865_; lean_object* v_tail_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1875_; 
v_head_1865_ = lean_ctor_get(v_x_1864_, 0);
v_tail_1866_ = lean_ctor_get(v_x_1864_, 1);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_x_1864_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1868_ = v_x_1864_;
v_isShared_1869_ = v_isSharedCheck_1875_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_tail_1866_);
lean_inc(v_head_1865_);
lean_dec(v_x_1864_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1875_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
lean_inc(v_x_1862_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set_tag(v___x_1868_, 5);
lean_ctor_set(v___x_1868_, 1, v_x_1862_);
lean_ctor_set(v___x_1868_, 0, v_x_1863_);
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_x_1863_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_x_1862_);
v___x_1871_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
lean_object* v___x_1872_; 
v___x_1872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v_head_1865_);
v_x_1863_ = v___x_1872_;
v_x_1864_ = v_tail_1866_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2_spec__3(lean_object* v_x_1876_, lean_object* v_x_1877_){
_start:
{
if (lean_obj_tag(v_x_1876_) == 0)
{
lean_object* v___x_1878_; 
lean_dec(v_x_1877_);
v___x_1878_ = lean_box(0);
return v___x_1878_;
}
else
{
lean_object* v_tail_1879_; 
v_tail_1879_ = lean_ctor_get(v_x_1876_, 1);
if (lean_obj_tag(v_tail_1879_) == 0)
{
lean_object* v_head_1880_; 
lean_dec(v_x_1877_);
v_head_1880_ = lean_ctor_get(v_x_1876_, 0);
lean_inc(v_head_1880_);
lean_dec_ref_known(v_x_1876_, 2);
return v_head_1880_;
}
else
{
lean_object* v_head_1881_; lean_object* v___x_1882_; 
lean_inc(v_tail_1879_);
v_head_1881_ = lean_ctor_get(v_x_1876_, 0);
lean_inc(v_head_1881_);
lean_dec_ref_known(v_x_1876_, 2);
v___x_1882_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2_spec__3_spec__5(v_x_1877_, v_head_1881_, v_tail_1879_);
return v___x_1882_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__0));
v___x_1886_ = lean_string_length(v___x_1885_);
return v___x_1886_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2, &l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2);
v___x_1888_ = lean_nat_to_int(v___x_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(lean_object* v_x_1893_){
_start:
{
lean_object* v_fst_1894_; lean_object* v_snd_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1918_; 
v_fst_1894_ = lean_ctor_get(v_x_1893_, 0);
v_snd_1895_ = lean_ctor_get(v_x_1893_, 1);
v_isSharedCheck_1918_ = !lean_is_exclusive(v_x_1893_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1897_ = v_x_1893_;
v_isShared_1898_ = v_isSharedCheck_1918_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_snd_1895_);
lean_inc(v_fst_1894_);
lean_dec(v_x_1893_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1918_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1899_ = lean_unsigned_to_nat(0u);
v___x_1900_ = l_Lean_Name_reprPrec(v_fst_1894_, v___x_1899_);
v___x_1901_ = lean_box(0);
if (v_isShared_1898_ == 0)
{
lean_ctor_set_tag(v___x_1897_, 1);
lean_ctor_set(v___x_1897_, 1, v___x_1901_);
lean_ctor_set(v___x_1897_, 0, v___x_1900_);
v___x_1903_ = v___x_1897_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1900_);
lean_ctor_set(v_reuseFailAlloc_1917_, 1, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; uint8_t v___x_1915_; lean_object* v___x_1916_; 
v___x_1904_ = l_Lean_instReprImportArtifacts_repr___redArg(v_snd_1895_);
v___x_1905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
lean_ctor_set(v___x_1905_, 1, v___x_1903_);
v___x_1906_ = l_List_reverse___redArg(v___x_1905_);
v___x_1907_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_1908_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2_spec__3(v___x_1906_, v___x_1907_);
v___x_1909_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3);
v___x_1910_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__4));
v___x_1911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
lean_ctor_set(v___x_1911_, 1, v___x_1908_);
v___x_1912_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__5));
v___x_1913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1911_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1909_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = 0;
v___x_1916_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1916_, 0, v___x_1914_);
lean_ctor_set_uint8(v___x_1916_, sizeof(void*)*1, v___x_1915_);
return v___x_1916_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3_spec__5_spec__8(lean_object* v_x_1919_, lean_object* v_x_1920_, lean_object* v_x_1921_){
_start:
{
if (lean_obj_tag(v_x_1921_) == 0)
{
lean_dec(v_x_1919_);
return v_x_1920_;
}
else
{
lean_object* v_head_1922_; lean_object* v_tail_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1933_; 
v_head_1922_ = lean_ctor_get(v_x_1921_, 0);
v_tail_1923_ = lean_ctor_get(v_x_1921_, 1);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_x_1921_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1925_ = v_x_1921_;
v_isShared_1926_ = v_isSharedCheck_1933_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_tail_1923_);
lean_inc(v_head_1922_);
lean_dec(v_x_1921_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1933_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
lean_inc(v_x_1919_);
if (v_isShared_1926_ == 0)
{
lean_ctor_set_tag(v___x_1925_, 5);
lean_ctor_set(v___x_1925_, 1, v_x_1919_);
lean_ctor_set(v___x_1925_, 0, v_x_1920_);
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_x_1920_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_x_1919_);
v___x_1928_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_head_1922_);
v___x_1930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1928_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v_x_1920_ = v___x_1930_;
v_x_1921_ = v_tail_1923_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3_spec__5(lean_object* v_x_1934_, lean_object* v_x_1935_, lean_object* v_x_1936_){
_start:
{
if (lean_obj_tag(v_x_1936_) == 0)
{
lean_dec(v_x_1934_);
return v_x_1935_;
}
else
{
lean_object* v_head_1937_; lean_object* v_tail_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1948_; 
v_head_1937_ = lean_ctor_get(v_x_1936_, 0);
v_tail_1938_ = lean_ctor_get(v_x_1936_, 1);
v_isSharedCheck_1948_ = !lean_is_exclusive(v_x_1936_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1940_ = v_x_1936_;
v_isShared_1941_ = v_isSharedCheck_1948_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_tail_1938_);
lean_inc(v_head_1937_);
lean_dec(v_x_1936_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1948_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
lean_inc(v_x_1934_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set_tag(v___x_1940_, 5);
lean_ctor_set(v___x_1940_, 1, v_x_1934_);
lean_ctor_set(v___x_1940_, 0, v_x_1935_);
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_x_1935_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_x_1934_);
v___x_1943_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1944_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_head_1937_);
v___x_1945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1943_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3_spec__5_spec__8(v_x_1934_, v___x_1945_, v_tail_1938_);
return v___x_1946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3(lean_object* v_x_1949_, lean_object* v_x_1950_){
_start:
{
if (lean_obj_tag(v_x_1949_) == 0)
{
lean_object* v___x_1951_; 
lean_dec(v_x_1950_);
v___x_1951_ = lean_box(0);
return v___x_1951_;
}
else
{
lean_object* v_tail_1952_; 
v_tail_1952_ = lean_ctor_get(v_x_1949_, 1);
if (lean_obj_tag(v_tail_1952_) == 0)
{
lean_object* v_head_1953_; lean_object* v___x_1954_; 
lean_dec(v_x_1950_);
v_head_1953_ = lean_ctor_get(v_x_1949_, 0);
lean_inc(v_head_1953_);
lean_dec_ref_known(v_x_1949_, 2);
v___x_1954_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_head_1953_);
return v___x_1954_;
}
else
{
lean_object* v_head_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
lean_inc(v_tail_1952_);
v_head_1955_ = lean_ctor_get(v_x_1949_, 0);
lean_inc(v_head_1955_);
lean_dec_ref_known(v_x_1949_, 2);
v___x_1956_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_head_1955_);
v___x_1957_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3_spec__5(v_x_1950_, v___x_1956_, v_tail_1952_);
return v___x_1957_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = ((lean_object*)(l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__2));
v___x_1963_ = lean_string_length(v___x_1962_);
return v___x_1963_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = lean_obj_once(&l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3, &l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3_once, _init_l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3);
v___x_1965_ = lean_nat_to_int(v___x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg(lean_object* v_a_1968_){
_start:
{
if (lean_obj_tag(v_a_1968_) == 0)
{
lean_object* v___x_1969_; 
v___x_1969_ = ((lean_object*)(l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__1));
return v___x_1969_;
}
else
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; lean_object* v___x_1979_; 
v___x_1970_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_1971_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3(v_a_1968_, v___x_1970_);
v___x_1972_ = lean_obj_once(&l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4, &l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4_once, _init_l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4);
v___x_1973_ = ((lean_object*)(l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__5));
v___x_1974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
lean_ctor_set(v___x_1974_, 1, v___x_1971_);
v___x_1975_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6));
v___x_1976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1974_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
v___x_1977_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1972_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = 0;
v___x_1979_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1979_, 0, v___x_1977_);
lean_ctor_set_uint8(v___x_1979_, sizeof(void*)*1, v___x_1978_);
return v___x_1979_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1(lean_object* v_init_1980_, lean_object* v_x_1981_){
_start:
{
if (lean_obj_tag(v_x_1981_) == 0)
{
lean_object* v_k_1982_; lean_object* v_v_1983_; lean_object* v_l_1984_; lean_object* v_r_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v_k_1982_ = lean_ctor_get(v_x_1981_, 1);
v_v_1983_ = lean_ctor_get(v_x_1981_, 2);
v_l_1984_ = lean_ctor_get(v_x_1981_, 3);
v_r_1985_ = lean_ctor_get(v_x_1981_, 4);
v___x_1986_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1(v_init_1980_, v_r_1985_);
lean_inc(v_v_1983_);
lean_inc(v_k_1982_);
v___x_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1987_, 0, v_k_1982_);
lean_ctor_set(v___x_1987_, 1, v_v_1983_);
v___x_1988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
lean_ctor_set(v___x_1988_, 1, v___x_1986_);
v_init_1980_ = v___x_1988_;
v_x_1981_ = v_l_1984_;
goto _start;
}
else
{
return v_init_1980_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1___boxed(lean_object* v_init_1990_, lean_object* v_x_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1(v_init_1990_, v_x_1991_);
lean_dec(v_x_1991_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5_spec__8_spec__11(lean_object* v_x_1993_, lean_object* v_x_1994_, lean_object* v_x_1995_){
_start:
{
if (lean_obj_tag(v_x_1995_) == 0)
{
lean_dec(v_x_1993_);
return v_x_1994_;
}
else
{
lean_object* v_head_1996_; lean_object* v_tail_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2007_; 
v_head_1996_ = lean_ctor_get(v_x_1995_, 0);
v_tail_1997_ = lean_ctor_get(v_x_1995_, 1);
v_isSharedCheck_2007_ = !lean_is_exclusive(v_x_1995_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1999_ = v_x_1995_;
v_isShared_2000_ = v_isSharedCheck_2007_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_tail_1997_);
lean_inc(v_head_1996_);
lean_dec(v_x_1995_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2007_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
lean_inc(v_x_1993_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set_tag(v___x_1999_, 5);
lean_ctor_set(v___x_1999_, 1, v_x_1993_);
lean_ctor_set(v___x_1999_, 0, v_x_1994_);
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_x_1994_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_x_1993_);
v___x_2002_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = l_Lean_instReprPlugin_repr___redArg(v_head_1996_);
v___x_2004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2002_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
v_x_1994_ = v___x_2004_;
v_x_1995_ = v_tail_1997_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5_spec__8(lean_object* v_x_2008_, lean_object* v_x_2009_, lean_object* v_x_2010_){
_start:
{
if (lean_obj_tag(v_x_2010_) == 0)
{
lean_dec(v_x_2008_);
return v_x_2009_;
}
else
{
lean_object* v_head_2011_; lean_object* v_tail_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2022_; 
v_head_2011_ = lean_ctor_get(v_x_2010_, 0);
v_tail_2012_ = lean_ctor_get(v_x_2010_, 1);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_x_2010_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2014_ = v_x_2010_;
v_isShared_2015_ = v_isSharedCheck_2022_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_tail_2012_);
lean_inc(v_head_2011_);
lean_dec(v_x_2010_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2022_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
lean_inc(v_x_2008_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set_tag(v___x_2014_, 5);
lean_ctor_set(v___x_2014_, 1, v_x_2008_);
lean_ctor_set(v___x_2014_, 0, v_x_2009_);
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_x_2009_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_x_2008_);
v___x_2017_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2018_ = l_Lean_instReprPlugin_repr___redArg(v_head_2011_);
v___x_2019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2017_);
lean_ctor_set(v___x_2019_, 1, v___x_2018_);
v___x_2020_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5_spec__8_spec__11(v_x_2008_, v___x_2019_, v_tail_2012_);
return v___x_2020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5(lean_object* v_x_2023_, lean_object* v_x_2024_){
_start:
{
if (lean_obj_tag(v_x_2023_) == 0)
{
lean_object* v___x_2025_; 
lean_dec(v_x_2024_);
v___x_2025_ = lean_box(0);
return v___x_2025_;
}
else
{
lean_object* v_tail_2026_; 
v_tail_2026_ = lean_ctor_get(v_x_2023_, 1);
if (lean_obj_tag(v_tail_2026_) == 0)
{
lean_object* v_head_2027_; lean_object* v___x_2028_; 
lean_dec(v_x_2024_);
v_head_2027_ = lean_ctor_get(v_x_2023_, 0);
lean_inc(v_head_2027_);
lean_dec_ref_known(v_x_2023_, 2);
v___x_2028_ = l_Lean_instReprPlugin_repr___redArg(v_head_2027_);
return v___x_2028_;
}
else
{
lean_object* v_head_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
lean_inc(v_tail_2026_);
v_head_2029_ = lean_ctor_get(v_x_2023_, 0);
lean_inc(v_head_2029_);
lean_dec_ref_known(v_x_2023_, 2);
v___x_2030_ = l_Lean_instReprPlugin_repr___redArg(v_head_2029_);
v___x_2031_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5_spec__8(v_x_2024_, v___x_2030_, v_tail_2026_);
return v___x_2031_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3(lean_object* v_xs_2032_){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2033_ = lean_array_get_size(v_xs_2032_);
v___x_2034_ = lean_unsigned_to_nat(0u);
v___x_2035_ = lean_nat_dec_eq(v___x_2033_, v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2036_ = lean_array_to_list(v_xs_2032_);
v___x_2037_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_2038_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5(v___x_2036_, v___x_2037_);
v___x_2039_ = lean_obj_once(&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4);
v___x_2040_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5));
v___x_2041_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
lean_ctor_set(v___x_2041_, 1, v___x_2038_);
v___x_2042_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6));
v___x_2043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2041_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
v___x_2044_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2039_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
v___x_2045_ = l_Std_Format_fill(v___x_2044_);
return v___x_2045_;
}
else
{
lean_object* v___x_2046_; 
lean_dec_ref(v_xs_2032_);
v___x_2046_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8));
return v___x_2046_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprModuleSetup_repr_spec__0(lean_object* v_x_2047_, lean_object* v_x_2048_){
_start:
{
if (lean_obj_tag(v_x_2047_) == 0)
{
lean_object* v___x_2049_; 
v___x_2049_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__1));
return v___x_2049_;
}
else
{
lean_object* v_val_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v_val_2050_ = lean_ctor_get(v_x_2047_, 0);
lean_inc(v_val_2050_);
lean_dec_ref_known(v_x_2047_, 1);
v___x_2051_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__3));
v___x_2052_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0(v_val_2050_);
v___x_2053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2051_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
v___x_2054_ = l_Repr_addAppParen(v___x_2053_, v_x_2048_);
return v___x_2054_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprModuleSetup_repr_spec__0___boxed(lean_object* v_x_2055_, lean_object* v_x_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Option_repr___at___00Lean_instReprModuleSetup_repr_spec__0(v_x_2055_, v_x_2056_);
lean_dec(v_x_2056_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleSetup_repr___redArg(lean_object* v_x_2088_){
_start:
{
lean_object* v_name_2089_; lean_object* v_package_x3f_2090_; uint8_t v_isModule_2091_; lean_object* v_imports_x3f_2092_; lean_object* v_importArts_2093_; lean_object* v_dynlibs_2094_; lean_object* v_plugins_2095_; lean_object* v_options_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v_name_2089_ = lean_ctor_get(v_x_2088_, 0);
lean_inc(v_name_2089_);
v_package_x3f_2090_ = lean_ctor_get(v_x_2088_, 1);
lean_inc(v_package_x3f_2090_);
v_isModule_2091_ = lean_ctor_get_uint8(v_x_2088_, sizeof(void*)*7);
v_imports_x3f_2092_ = lean_ctor_get(v_x_2088_, 2);
lean_inc(v_imports_x3f_2092_);
v_importArts_2093_ = lean_ctor_get(v_x_2088_, 3);
lean_inc(v_importArts_2093_);
v_dynlibs_2094_ = lean_ctor_get(v_x_2088_, 4);
lean_inc_ref(v_dynlibs_2094_);
v_plugins_2095_ = lean_ctor_get(v_x_2088_, 5);
lean_inc_ref(v_plugins_2095_);
v_options_2096_ = lean_ctor_get(v_x_2088_, 6);
lean_inc(v_options_2096_);
lean_dec_ref(v_x_2088_);
v___x_2097_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__5));
v___x_2098_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__3));
v___x_2099_ = lean_obj_once(&l_Lean_instReprPlugin_repr___redArg___closed__4, &l_Lean_instReprPlugin_repr___redArg___closed__4_once, _init_l_Lean_instReprPlugin_repr___redArg___closed__4);
v___x_2100_ = lean_unsigned_to_nat(0u);
v___x_2101_ = l_Lean_Name_reprPrec(v_name_2089_, v___x_2100_);
v___x_2102_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2099_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
v___x_2103_ = 0;
v___x_2104_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2104_, 0, v___x_2102_);
lean_ctor_set_uint8(v___x_2104_, sizeof(void*)*1, v___x_2103_);
v___x_2105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2098_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
v___x_2106_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__9));
v___x_2107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2105_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
v___x_2108_ = lean_box(1);
v___x_2109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2107_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
v___x_2110_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__5));
v___x_2111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2109_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
v___x_2112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
lean_ctor_set(v___x_2112_, 1, v___x_2097_);
v___x_2113_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__7, &l_Lean_instReprModuleHeader_repr___redArg___closed__7_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__7);
v___x_2114_ = l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0(v_package_x3f_2090_, v___x_2100_);
v___x_2115_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2113_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___x_2116_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
lean_ctor_set_uint8(v___x_2116_, sizeof(void*)*1, v___x_2103_);
v___x_2117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2112_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v___x_2118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v___x_2106_);
v___x_2119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
lean_ctor_set(v___x_2119_, 1, v___x_2108_);
v___x_2120_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__6));
v___x_2121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2119_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
lean_ctor_set(v___x_2122_, 1, v___x_2097_);
v___x_2123_ = l_Bool_repr___redArg(v_isModule_2091_);
v___x_2124_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2113_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
lean_ctor_set_uint8(v___x_2125_, sizeof(void*)*1, v___x_2103_);
v___x_2126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2122_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_ctor_set(v___x_2127_, 1, v___x_2106_);
v___x_2128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
lean_ctor_set(v___x_2128_, 1, v___x_2108_);
v___x_2129_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__7));
v___x_2130_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2128_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
lean_ctor_set(v___x_2131_, 1, v___x_2097_);
v___x_2132_ = l_Option_repr___at___00Lean_instReprModuleSetup_repr_spec__0(v_imports_x3f_2092_, v___x_2100_);
v___x_2133_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2113_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
lean_ctor_set_uint8(v___x_2134_, sizeof(void*)*1, v___x_2103_);
v___x_2135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2131_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
v___x_2136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
lean_ctor_set(v___x_2136_, 1, v___x_2106_);
v___x_2137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2136_);
lean_ctor_set(v___x_2137_, 1, v___x_2108_);
v___x_2138_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__9));
v___x_2139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2137_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
v___x_2140_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
lean_ctor_set(v___x_2140_, 1, v___x_2097_);
v___x_2141_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__15, &l_Lean_instReprImport_repr___redArg___closed__15_once, _init_l_Lean_instReprImport_repr___redArg___closed__15);
v___x_2142_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__11));
v___x_2143_ = lean_box(0);
v___x_2144_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1(v___x_2143_, v_importArts_2093_);
lean_dec(v_importArts_2093_);
v___x_2145_ = l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg(v___x_2144_);
v___x_2146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2142_);
lean_ctor_set(v___x_2146_, 1, v___x_2145_);
v___x_2147_ = l_Repr_addAppParen(v___x_2146_, v___x_2100_);
v___x_2148_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2141_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
v___x_2149_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2149_, 0, v___x_2148_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*1, v___x_2103_);
v___x_2150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2140_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
lean_ctor_set(v___x_2151_, 1, v___x_2106_);
v___x_2152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
lean_ctor_set(v___x_2152_, 1, v___x_2108_);
v___x_2153_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__13));
v___x_2154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2152_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
lean_ctor_set(v___x_2155_, 1, v___x_2097_);
v___x_2156_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__4, &l_Lean_instReprModuleHeader_repr___redArg___closed__4_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__4);
v___x_2157_ = l_Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0(v_dynlibs_2094_);
v___x_2158_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2156_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
lean_ctor_set_uint8(v___x_2159_, sizeof(void*)*1, v___x_2103_);
v___x_2160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2155_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
lean_ctor_set(v___x_2161_, 1, v___x_2106_);
v___x_2162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
lean_ctor_set(v___x_2162_, 1, v___x_2108_);
v___x_2163_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__15));
v___x_2164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2162_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
lean_ctor_set(v___x_2165_, 1, v___x_2097_);
v___x_2166_ = l_Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3(v_plugins_2095_);
v___x_2167_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2156_);
lean_ctor_set(v___x_2167_, 1, v___x_2166_);
v___x_2168_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
lean_ctor_set_uint8(v___x_2168_, sizeof(void*)*1, v___x_2103_);
v___x_2169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2165_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
v___x_2170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2169_);
lean_ctor_set(v___x_2170_, 1, v___x_2106_);
v___x_2171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
lean_ctor_set(v___x_2171_, 1, v___x_2108_);
v___x_2172_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__17));
v___x_2173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2171_);
lean_ctor_set(v___x_2173_, 1, v___x_2172_);
v___x_2174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
lean_ctor_set(v___x_2174_, 1, v___x_2097_);
v___x_2175_ = l_Lean_instReprLeanOptions_repr___redArg(v_options_2096_);
lean_dec(v_options_2096_);
v___x_2176_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2156_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
v___x_2177_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
lean_ctor_set_uint8(v___x_2177_, sizeof(void*)*1, v___x_2103_);
v___x_2178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2174_);
lean_ctor_set(v___x_2178_, 1, v___x_2177_);
v___x_2179_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__20, &l_Lean_instReprImport_repr___redArg___closed__20_once, _init_l_Lean_instReprImport_repr___redArg___closed__20);
v___x_2180_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__21));
v___x_2181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2180_);
lean_ctor_set(v___x_2181_, 1, v___x_2178_);
v___x_2182_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__22));
v___x_2183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2181_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
v___x_2184_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2179_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
v___x_2185_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
lean_ctor_set_uint8(v___x_2185_, sizeof(void*)*1, v___x_2103_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleSetup_repr(lean_object* v_x_2186_, lean_object* v_prec_2187_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l_Lean_instReprModuleSetup_repr___redArg(v_x_2186_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleSetup_repr___boxed(lean_object* v_x_2189_, lean_object* v_prec_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Lean_instReprModuleSetup_repr(v_x_2189_, v_prec_2190_);
lean_dec(v_prec_2190_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2(lean_object* v_a_2192_, lean_object* v_n_2193_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg(v_a_2192_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___boxed(lean_object* v_a_2195_, lean_object* v_n_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2(v_a_2195_, v_n_2196_);
lean_dec(v_n_2196_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2(lean_object* v_x_2198_, lean_object* v_x_2199_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_x_2198_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___boxed(lean_object* v_x_2201_, lean_object* v_x_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2(v_x_2201_, v_x_2202_);
lean_dec(v_x_2202_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__5(size_t v_sz_2214_, size_t v_i_2215_, lean_object* v_bs_2216_){
_start:
{
uint8_t v___x_2217_; 
v___x_2217_ = lean_usize_dec_lt(v_i_2215_, v_sz_2214_);
if (v___x_2217_ == 0)
{
return v_bs_2216_;
}
else
{
lean_object* v_v_2218_; lean_object* v___x_2219_; lean_object* v_bs_x27_2220_; lean_object* v___x_2221_; size_t v___x_2222_; size_t v___x_2223_; lean_object* v___x_2224_; 
v_v_2218_ = lean_array_uget(v_bs_2216_, v_i_2215_);
v___x_2219_ = lean_unsigned_to_nat(0u);
v_bs_x27_2220_ = lean_array_uset(v_bs_2216_, v_i_2215_, v___x_2219_);
v___x_2221_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2221_, 0, v_v_2218_);
v___x_2222_ = ((size_t)1ULL);
v___x_2223_ = lean_usize_add(v_i_2215_, v___x_2222_);
v___x_2224_ = lean_array_uset(v_bs_x27_2220_, v_i_2215_, v___x_2221_);
v_i_2215_ = v___x_2223_;
v_bs_2216_ = v___x_2224_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__5___boxed(lean_object* v_sz_2226_, lean_object* v_i_2227_, lean_object* v_bs_2228_){
_start:
{
size_t v_sz_boxed_2229_; size_t v_i_boxed_2230_; lean_object* v_res_2231_; 
v_sz_boxed_2229_ = lean_unbox_usize(v_sz_2226_);
lean_dec(v_sz_2226_);
v_i_boxed_2230_ = lean_unbox_usize(v_i_2227_);
lean_dec(v_i_2227_);
v_res_2231_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__5(v_sz_boxed_2229_, v_i_boxed_2230_, v_bs_2228_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2(lean_object* v_a_2232_){
_start:
{
size_t v_sz_2233_; size_t v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v_sz_2233_ = lean_array_size(v_a_2232_);
v___x_2234_ = ((size_t)0ULL);
v___x_2235_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__5(v_sz_2233_, v___x_2234_, v_a_2232_);
v___x_2236_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2(size_t v_sz_2237_, size_t v_i_2238_, lean_object* v_bs_2239_){
_start:
{
uint8_t v___x_2240_; 
v___x_2240_ = lean_usize_dec_lt(v_i_2238_, v_sz_2237_);
if (v___x_2240_ == 0)
{
return v_bs_2239_;
}
else
{
lean_object* v_v_2241_; lean_object* v___x_2242_; lean_object* v_bs_x27_2243_; lean_object* v___x_2244_; size_t v___x_2245_; size_t v___x_2246_; lean_object* v___x_2247_; 
v_v_2241_ = lean_array_uget(v_bs_2239_, v_i_2238_);
v___x_2242_ = lean_unsigned_to_nat(0u);
v_bs_x27_2243_ = lean_array_uset(v_bs_2239_, v_i_2238_, v___x_2242_);
v___x_2244_ = l_Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2(v_v_2241_);
v___x_2245_ = ((size_t)1ULL);
v___x_2246_ = lean_usize_add(v_i_2238_, v___x_2245_);
v___x_2247_ = lean_array_uset(v_bs_x27_2243_, v_i_2238_, v___x_2244_);
v_i_2238_ = v___x_2246_;
v_bs_2239_ = v___x_2247_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2249_, lean_object* v_i_2250_, lean_object* v_bs_2251_){
_start:
{
size_t v_sz_boxed_2252_; size_t v_i_boxed_2253_; lean_object* v_res_2254_; 
v_sz_boxed_2252_ = lean_unbox_usize(v_sz_2249_);
lean_dec(v_sz_2249_);
v_i_boxed_2253_ = lean_unbox_usize(v_i_2250_);
lean_dec(v_i_2250_);
v_res_2254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2(v_sz_boxed_2252_, v_i_boxed_2253_, v_bs_2251_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1(lean_object* v_a_2255_){
_start:
{
size_t v_sz_2256_; size_t v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v_sz_2256_ = lean_array_size(v_a_2255_);
v___x_2257_ = ((size_t)0ULL);
v___x_2258_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2(v_sz_2256_, v___x_2257_, v_a_2255_);
v___x_2259_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4___redArg(lean_object* v_msg_2260_){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = lean_box(1);
v___x_2262_ = lean_panic_fn_borrowed(v___x_2261_, v_msg_2260_);
return v___x_2262_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2266_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__2));
v___x_2267_ = lean_unsigned_to_nat(35u);
v___x_2268_ = lean_unsigned_to_nat(182u);
v___x_2269_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__1));
v___x_2270_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__0));
v___x_2271_ = l_mkPanicMessageWithDecl(v___x_2270_, v___x_2269_, v___x_2268_, v___x_2267_, v___x_2266_);
return v___x_2271_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2272_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__2));
v___x_2273_ = lean_unsigned_to_nat(21u);
v___x_2274_ = lean_unsigned_to_nat(183u);
v___x_2275_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__1));
v___x_2276_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__0));
v___x_2277_ = l_mkPanicMessageWithDecl(v___x_2276_, v___x_2275_, v___x_2274_, v___x_2273_, v___x_2272_);
return v___x_2277_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2280_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__6));
v___x_2281_ = lean_unsigned_to_nat(35u);
v___x_2282_ = lean_unsigned_to_nat(276u);
v___x_2283_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__5));
v___x_2284_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__0));
v___x_2285_ = l_mkPanicMessageWithDecl(v___x_2284_, v___x_2283_, v___x_2282_, v___x_2281_, v___x_2280_);
return v___x_2285_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2286_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__6));
v___x_2287_ = lean_unsigned_to_nat(21u);
v___x_2288_ = lean_unsigned_to_nat(277u);
v___x_2289_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__5));
v___x_2290_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__0));
v___x_2291_ = l_mkPanicMessageWithDecl(v___x_2290_, v___x_2289_, v___x_2288_, v___x_2287_, v___x_2286_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg(lean_object* v_k_2292_, lean_object* v_v_2293_, lean_object* v_t_2294_){
_start:
{
if (lean_obj_tag(v_t_2294_) == 0)
{
lean_object* v_size_2295_; lean_object* v_k_2296_; lean_object* v_v_2297_; lean_object* v_l_2298_; lean_object* v_r_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2655_; 
v_size_2295_ = lean_ctor_get(v_t_2294_, 0);
v_k_2296_ = lean_ctor_get(v_t_2294_, 1);
v_v_2297_ = lean_ctor_get(v_t_2294_, 2);
v_l_2298_ = lean_ctor_get(v_t_2294_, 3);
v_r_2299_ = lean_ctor_get(v_t_2294_, 4);
v_isSharedCheck_2655_ = !lean_is_exclusive(v_t_2294_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2301_ = v_t_2294_;
v_isShared_2302_ = v_isSharedCheck_2655_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_r_2299_);
lean_inc(v_l_2298_);
lean_inc(v_v_2297_);
lean_inc(v_k_2296_);
lean_inc(v_size_2295_);
lean_dec(v_t_2294_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2655_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
uint8_t v___x_2303_; 
v___x_2303_ = lean_string_compare(v_k_2292_, v_k_2296_);
switch(v___x_2303_)
{
case 0:
{
lean_object* v___x_2304_; 
lean_dec(v_size_2295_);
v___x_2304_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg(v_k_2292_, v_v_2293_, v_l_2298_);
if (lean_obj_tag(v_r_2299_) == 0)
{
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_size_2305_; lean_object* v_size_2306_; lean_object* v_k_2307_; lean_object* v_v_2308_; lean_object* v_l_2309_; lean_object* v_r_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; uint8_t v___x_2313_; 
v_size_2305_ = lean_ctor_get(v_r_2299_, 0);
v_size_2306_ = lean_ctor_get(v___x_2304_, 0);
v_k_2307_ = lean_ctor_get(v___x_2304_, 1);
v_v_2308_ = lean_ctor_get(v___x_2304_, 2);
v_l_2309_ = lean_ctor_get(v___x_2304_, 3);
v_r_2310_ = lean_ctor_get(v___x_2304_, 4);
lean_inc(v_r_2310_);
v___x_2311_ = lean_unsigned_to_nat(3u);
v___x_2312_ = lean_nat_mul(v___x_2311_, v_size_2305_);
v___x_2313_ = lean_nat_dec_lt(v___x_2312_, v_size_2306_);
lean_dec(v___x_2312_);
if (v___x_2313_ == 0)
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2318_; 
lean_dec(v_r_2310_);
v___x_2314_ = lean_unsigned_to_nat(1u);
v___x_2315_ = lean_nat_add(v___x_2314_, v_size_2306_);
v___x_2316_ = lean_nat_add(v___x_2315_, v_size_2305_);
lean_dec(v___x_2315_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 3, v___x_2304_);
lean_ctor_set(v___x_2301_, 0, v___x_2316_);
v___x_2318_ = v___x_2301_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2319_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2319_, 3, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2319_, 4, v_r_2299_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
else
{
lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2391_; 
lean_inc(v_l_2309_);
lean_inc(v_v_2308_);
lean_inc(v_k_2307_);
lean_inc(v_size_2306_);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2391_ == 0)
{
lean_object* v_unused_2392_; lean_object* v_unused_2393_; lean_object* v_unused_2394_; lean_object* v_unused_2395_; lean_object* v_unused_2396_; 
v_unused_2392_ = lean_ctor_get(v___x_2304_, 4);
lean_dec(v_unused_2392_);
v_unused_2393_ = lean_ctor_get(v___x_2304_, 3);
lean_dec(v_unused_2393_);
v_unused_2394_ = lean_ctor_get(v___x_2304_, 2);
lean_dec(v_unused_2394_);
v_unused_2395_ = lean_ctor_get(v___x_2304_, 1);
lean_dec(v_unused_2395_);
v_unused_2396_ = lean_ctor_get(v___x_2304_, 0);
lean_dec(v_unused_2396_);
v___x_2321_ = v___x_2304_;
v_isShared_2322_ = v_isSharedCheck_2391_;
goto v_resetjp_2320_;
}
else
{
lean_dec(v___x_2304_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2391_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
if (lean_obj_tag(v_l_2309_) == 0)
{
if (lean_obj_tag(v_r_2310_) == 0)
{
lean_object* v_size_2323_; lean_object* v_size_2324_; lean_object* v_k_2325_; lean_object* v_v_2326_; lean_object* v_l_2327_; lean_object* v_r_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v_size_2323_ = lean_ctor_get(v_l_2309_, 0);
v_size_2324_ = lean_ctor_get(v_r_2310_, 0);
v_k_2325_ = lean_ctor_get(v_r_2310_, 1);
v_v_2326_ = lean_ctor_get(v_r_2310_, 2);
v_l_2327_ = lean_ctor_get(v_r_2310_, 3);
v_r_2328_ = lean_ctor_get(v_r_2310_, 4);
v___x_2329_ = lean_unsigned_to_nat(2u);
v___x_2330_ = lean_nat_mul(v___x_2329_, v_size_2323_);
v___x_2331_ = lean_nat_dec_lt(v_size_2324_, v___x_2330_);
lean_dec(v___x_2330_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2361_; 
lean_inc(v_r_2328_);
lean_inc(v_l_2327_);
lean_inc(v_v_2326_);
lean_inc(v_k_2325_);
v_isSharedCheck_2361_ = !lean_is_exclusive(v_r_2310_);
if (v_isSharedCheck_2361_ == 0)
{
lean_object* v_unused_2362_; lean_object* v_unused_2363_; lean_object* v_unused_2364_; lean_object* v_unused_2365_; lean_object* v_unused_2366_; 
v_unused_2362_ = lean_ctor_get(v_r_2310_, 4);
lean_dec(v_unused_2362_);
v_unused_2363_ = lean_ctor_get(v_r_2310_, 3);
lean_dec(v_unused_2363_);
v_unused_2364_ = lean_ctor_get(v_r_2310_, 2);
lean_dec(v_unused_2364_);
v_unused_2365_ = lean_ctor_get(v_r_2310_, 1);
lean_dec(v_unused_2365_);
v_unused_2366_ = lean_ctor_get(v_r_2310_, 0);
lean_dec(v_unused_2366_);
v___x_2333_ = v_r_2310_;
v_isShared_2334_ = v_isSharedCheck_2361_;
goto v_resetjp_2332_;
}
else
{
lean_dec(v_r_2310_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2361_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___x_2349_; lean_object* v___y_2351_; 
v___x_2335_ = lean_unsigned_to_nat(1u);
v___x_2336_ = lean_nat_add(v___x_2335_, v_size_2306_);
lean_dec(v_size_2306_);
v___x_2337_ = lean_nat_add(v___x_2336_, v_size_2305_);
lean_dec(v___x_2336_);
v___x_2349_ = lean_nat_add(v___x_2335_, v_size_2323_);
if (lean_obj_tag(v_l_2327_) == 0)
{
lean_object* v_size_2359_; 
v_size_2359_ = lean_ctor_get(v_l_2327_, 0);
lean_inc(v_size_2359_);
v___y_2351_ = v_size_2359_;
goto v___jp_2350_;
}
else
{
lean_object* v___x_2360_; 
v___x_2360_ = lean_unsigned_to_nat(0u);
v___y_2351_ = v___x_2360_;
goto v___jp_2350_;
}
v___jp_2338_:
{
lean_object* v___x_2342_; lean_object* v___x_2344_; 
v___x_2342_ = lean_nat_add(v___y_2339_, v___y_2341_);
lean_dec(v___y_2341_);
lean_dec(v___y_2339_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 4, v_r_2299_);
lean_ctor_set(v___x_2333_, 3, v_r_2328_);
lean_ctor_set(v___x_2333_, 2, v_v_2297_);
lean_ctor_set(v___x_2333_, 1, v_k_2296_);
lean_ctor_set(v___x_2333_, 0, v___x_2342_);
v___x_2344_ = v___x_2333_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2342_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2348_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2348_, 3, v_r_2328_);
lean_ctor_set(v_reuseFailAlloc_2348_, 4, v_r_2299_);
v___x_2344_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2346_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 4, v___x_2344_);
lean_ctor_set(v___x_2321_, 3, v___y_2340_);
lean_ctor_set(v___x_2321_, 2, v_v_2326_);
lean_ctor_set(v___x_2321_, 1, v_k_2325_);
lean_ctor_set(v___x_2321_, 0, v___x_2337_);
v___x_2346_ = v___x_2321_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2337_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_k_2325_);
lean_ctor_set(v_reuseFailAlloc_2347_, 2, v_v_2326_);
lean_ctor_set(v_reuseFailAlloc_2347_, 3, v___y_2340_);
lean_ctor_set(v_reuseFailAlloc_2347_, 4, v___x_2344_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
v___jp_2350_:
{
lean_object* v___x_2352_; lean_object* v___x_2354_; 
v___x_2352_ = lean_nat_add(v___x_2349_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec(v___x_2349_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v_l_2327_);
lean_ctor_set(v___x_2301_, 3, v_l_2309_);
lean_ctor_set(v___x_2301_, 2, v_v_2308_);
lean_ctor_set(v___x_2301_, 1, v_k_2307_);
lean_ctor_set(v___x_2301_, 0, v___x_2352_);
v___x_2354_ = v___x_2301_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2352_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_k_2307_);
lean_ctor_set(v_reuseFailAlloc_2358_, 2, v_v_2308_);
lean_ctor_set(v_reuseFailAlloc_2358_, 3, v_l_2309_);
lean_ctor_set(v_reuseFailAlloc_2358_, 4, v_l_2327_);
v___x_2354_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
lean_object* v___x_2355_; 
v___x_2355_ = lean_nat_add(v___x_2335_, v_size_2305_);
if (lean_obj_tag(v_r_2328_) == 0)
{
lean_object* v_size_2356_; 
v_size_2356_ = lean_ctor_get(v_r_2328_, 0);
lean_inc(v_size_2356_);
v___y_2339_ = v___x_2355_;
v___y_2340_ = v___x_2354_;
v___y_2341_ = v_size_2356_;
goto v___jp_2338_;
}
else
{
lean_object* v___x_2357_; 
v___x_2357_ = lean_unsigned_to_nat(0u);
v___y_2339_ = v___x_2355_;
v___y_2340_ = v___x_2354_;
v___y_2341_ = v___x_2357_;
goto v___jp_2338_;
}
}
}
}
}
else
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2373_; 
lean_del_object(v___x_2301_);
v___x_2367_ = lean_unsigned_to_nat(1u);
v___x_2368_ = lean_nat_add(v___x_2367_, v_size_2306_);
lean_dec(v_size_2306_);
v___x_2369_ = lean_nat_add(v___x_2368_, v_size_2305_);
lean_dec(v___x_2368_);
v___x_2370_ = lean_nat_add(v___x_2367_, v_size_2305_);
v___x_2371_ = lean_nat_add(v___x_2370_, v_size_2324_);
lean_dec(v___x_2370_);
lean_inc_ref(v_r_2299_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 4, v_r_2299_);
lean_ctor_set(v___x_2321_, 3, v_r_2310_);
lean_ctor_set(v___x_2321_, 2, v_v_2297_);
lean_ctor_set(v___x_2321_, 1, v_k_2296_);
lean_ctor_set(v___x_2321_, 0, v___x_2371_);
v___x_2373_ = v___x_2321_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2371_);
lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2386_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2386_, 3, v_r_2310_);
lean_ctor_set(v_reuseFailAlloc_2386_, 4, v_r_2299_);
v___x_2373_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
v_isSharedCheck_2380_ = !lean_is_exclusive(v_r_2299_);
if (v_isSharedCheck_2380_ == 0)
{
lean_object* v_unused_2381_; lean_object* v_unused_2382_; lean_object* v_unused_2383_; lean_object* v_unused_2384_; lean_object* v_unused_2385_; 
v_unused_2381_ = lean_ctor_get(v_r_2299_, 4);
lean_dec(v_unused_2381_);
v_unused_2382_ = lean_ctor_get(v_r_2299_, 3);
lean_dec(v_unused_2382_);
v_unused_2383_ = lean_ctor_get(v_r_2299_, 2);
lean_dec(v_unused_2383_);
v_unused_2384_ = lean_ctor_get(v_r_2299_, 1);
lean_dec(v_unused_2384_);
v_unused_2385_ = lean_ctor_get(v_r_2299_, 0);
lean_dec(v_unused_2385_);
v___x_2375_ = v_r_2299_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_dec(v_r_2299_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 4, v___x_2373_);
lean_ctor_set(v___x_2375_, 3, v_l_2309_);
lean_ctor_set(v___x_2375_, 2, v_v_2308_);
lean_ctor_set(v___x_2375_, 1, v_k_2307_);
lean_ctor_set(v___x_2375_, 0, v___x_2369_);
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2369_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v_k_2307_);
lean_ctor_set(v_reuseFailAlloc_2379_, 2, v_v_2308_);
lean_ctor_set(v_reuseFailAlloc_2379_, 3, v_l_2309_);
lean_ctor_set(v_reuseFailAlloc_2379_, 4, v___x_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
else
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
lean_dec_ref_known(v_l_2309_, 5);
lean_del_object(v___x_2321_);
lean_dec(v_v_2308_);
lean_dec(v_k_2307_);
lean_dec(v_size_2306_);
lean_dec_ref_known(v_r_2299_, 5);
lean_del_object(v___x_2301_);
lean_dec(v_v_2297_);
lean_dec(v_k_2296_);
v___x_2387_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__3);
v___x_2388_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4___redArg(v___x_2387_);
return v___x_2388_;
}
}
else
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
lean_del_object(v___x_2321_);
lean_dec(v_r_2310_);
lean_dec(v_v_2308_);
lean_dec(v_k_2307_);
lean_dec(v_size_2306_);
lean_dec_ref_known(v_r_2299_, 5);
lean_del_object(v___x_2301_);
lean_dec(v_v_2297_);
lean_dec(v_k_2296_);
v___x_2389_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__4);
v___x_2390_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4___redArg(v___x_2389_);
return v___x_2390_;
}
}
}
}
else
{
lean_object* v_size_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2401_; 
v_size_2397_ = lean_ctor_get(v_r_2299_, 0);
v___x_2398_ = lean_unsigned_to_nat(1u);
v___x_2399_ = lean_nat_add(v___x_2398_, v_size_2397_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 3, v___x_2304_);
lean_ctor_set(v___x_2301_, 0, v___x_2399_);
v___x_2401_ = v___x_2301_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2399_);
lean_ctor_set(v_reuseFailAlloc_2402_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2402_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2402_, 3, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2402_, 4, v_r_2299_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
else
{
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_l_2403_; 
v_l_2403_ = lean_ctor_get(v___x_2304_, 3);
if (lean_obj_tag(v_l_2403_) == 0)
{
lean_object* v_r_2404_; 
lean_inc_ref(v_l_2403_);
v_r_2404_ = lean_ctor_get(v___x_2304_, 4);
lean_inc(v_r_2404_);
if (lean_obj_tag(v_r_2404_) == 0)
{
lean_object* v_size_2405_; lean_object* v_k_2406_; lean_object* v_v_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2421_; 
v_size_2405_ = lean_ctor_get(v___x_2304_, 0);
v_k_2406_ = lean_ctor_get(v___x_2304_, 1);
v_v_2407_ = lean_ctor_get(v___x_2304_, 2);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2421_ == 0)
{
lean_object* v_unused_2422_; lean_object* v_unused_2423_; 
v_unused_2422_ = lean_ctor_get(v___x_2304_, 4);
lean_dec(v_unused_2422_);
v_unused_2423_ = lean_ctor_get(v___x_2304_, 3);
lean_dec(v_unused_2423_);
v___x_2409_ = v___x_2304_;
v_isShared_2410_ = v_isSharedCheck_2421_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_v_2407_);
lean_inc(v_k_2406_);
lean_inc(v_size_2405_);
lean_dec(v___x_2304_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2421_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v_size_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2416_; 
v_size_2411_ = lean_ctor_get(v_r_2404_, 0);
v___x_2412_ = lean_unsigned_to_nat(1u);
v___x_2413_ = lean_nat_add(v___x_2412_, v_size_2405_);
lean_dec(v_size_2405_);
v___x_2414_ = lean_nat_add(v___x_2412_, v_size_2411_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 4, v_r_2299_);
lean_ctor_set(v___x_2409_, 3, v_r_2404_);
lean_ctor_set(v___x_2409_, 2, v_v_2297_);
lean_ctor_set(v___x_2409_, 1, v_k_2296_);
lean_ctor_set(v___x_2409_, 0, v___x_2414_);
v___x_2416_ = v___x_2409_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2420_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2420_, 3, v_r_2404_);
lean_ctor_set(v_reuseFailAlloc_2420_, 4, v_r_2299_);
v___x_2416_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_object* v___x_2418_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v___x_2416_);
lean_ctor_set(v___x_2301_, 3, v_l_2403_);
lean_ctor_set(v___x_2301_, 2, v_v_2407_);
lean_ctor_set(v___x_2301_, 1, v_k_2406_);
lean_ctor_set(v___x_2301_, 0, v___x_2413_);
v___x_2418_ = v___x_2301_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v_k_2406_);
lean_ctor_set(v_reuseFailAlloc_2419_, 2, v_v_2407_);
lean_ctor_set(v_reuseFailAlloc_2419_, 3, v_l_2403_);
lean_ctor_set(v_reuseFailAlloc_2419_, 4, v___x_2416_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
else
{
lean_object* v_k_2424_; lean_object* v_v_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2437_; 
v_k_2424_ = lean_ctor_get(v___x_2304_, 1);
v_v_2425_ = lean_ctor_get(v___x_2304_, 2);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2437_ == 0)
{
lean_object* v_unused_2438_; lean_object* v_unused_2439_; lean_object* v_unused_2440_; 
v_unused_2438_ = lean_ctor_get(v___x_2304_, 4);
lean_dec(v_unused_2438_);
v_unused_2439_ = lean_ctor_get(v___x_2304_, 3);
lean_dec(v_unused_2439_);
v_unused_2440_ = lean_ctor_get(v___x_2304_, 0);
lean_dec(v_unused_2440_);
v___x_2427_ = v___x_2304_;
v_isShared_2428_ = v_isSharedCheck_2437_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_v_2425_);
lean_inc(v_k_2424_);
lean_dec(v___x_2304_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2437_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2432_; 
v___x_2429_ = lean_unsigned_to_nat(3u);
v___x_2430_ = lean_unsigned_to_nat(1u);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 3, v_r_2404_);
lean_ctor_set(v___x_2427_, 2, v_v_2297_);
lean_ctor_set(v___x_2427_, 1, v_k_2296_);
lean_ctor_set(v___x_2427_, 0, v___x_2430_);
v___x_2432_ = v___x_2427_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2430_);
lean_ctor_set(v_reuseFailAlloc_2436_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2436_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2436_, 3, v_r_2404_);
lean_ctor_set(v_reuseFailAlloc_2436_, 4, v_r_2404_);
v___x_2432_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
lean_object* v___x_2434_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v___x_2432_);
lean_ctor_set(v___x_2301_, 3, v_l_2403_);
lean_ctor_set(v___x_2301_, 2, v_v_2425_);
lean_ctor_set(v___x_2301_, 1, v_k_2424_);
lean_ctor_set(v___x_2301_, 0, v___x_2429_);
v___x_2434_ = v___x_2301_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2429_);
lean_ctor_set(v_reuseFailAlloc_2435_, 1, v_k_2424_);
lean_ctor_set(v_reuseFailAlloc_2435_, 2, v_v_2425_);
lean_ctor_set(v_reuseFailAlloc_2435_, 3, v_l_2403_);
lean_ctor_set(v_reuseFailAlloc_2435_, 4, v___x_2432_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
}
else
{
lean_object* v_r_2441_; 
v_r_2441_ = lean_ctor_get(v___x_2304_, 4);
lean_inc(v_r_2441_);
if (lean_obj_tag(v_r_2441_) == 0)
{
lean_object* v_k_2442_; lean_object* v_v_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2467_; 
lean_inc(v_l_2403_);
v_k_2442_ = lean_ctor_get(v___x_2304_, 1);
v_v_2443_ = lean_ctor_get(v___x_2304_, 2);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2467_ == 0)
{
lean_object* v_unused_2468_; lean_object* v_unused_2469_; lean_object* v_unused_2470_; 
v_unused_2468_ = lean_ctor_get(v___x_2304_, 4);
lean_dec(v_unused_2468_);
v_unused_2469_ = lean_ctor_get(v___x_2304_, 3);
lean_dec(v_unused_2469_);
v_unused_2470_ = lean_ctor_get(v___x_2304_, 0);
lean_dec(v_unused_2470_);
v___x_2445_ = v___x_2304_;
v_isShared_2446_ = v_isSharedCheck_2467_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_v_2443_);
lean_inc(v_k_2442_);
lean_dec(v___x_2304_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2467_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v_k_2447_; lean_object* v_v_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2463_; 
v_k_2447_ = lean_ctor_get(v_r_2441_, 1);
v_v_2448_ = lean_ctor_get(v_r_2441_, 2);
v_isSharedCheck_2463_ = !lean_is_exclusive(v_r_2441_);
if (v_isSharedCheck_2463_ == 0)
{
lean_object* v_unused_2464_; lean_object* v_unused_2465_; lean_object* v_unused_2466_; 
v_unused_2464_ = lean_ctor_get(v_r_2441_, 4);
lean_dec(v_unused_2464_);
v_unused_2465_ = lean_ctor_get(v_r_2441_, 3);
lean_dec(v_unused_2465_);
v_unused_2466_ = lean_ctor_get(v_r_2441_, 0);
lean_dec(v_unused_2466_);
v___x_2450_ = v_r_2441_;
v_isShared_2451_ = v_isSharedCheck_2463_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_v_2448_);
lean_inc(v_k_2447_);
lean_dec(v_r_2441_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2463_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2455_; 
v___x_2452_ = lean_unsigned_to_nat(3u);
v___x_2453_ = lean_unsigned_to_nat(1u);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 4, v_l_2403_);
lean_ctor_set(v___x_2450_, 3, v_l_2403_);
lean_ctor_set(v___x_2450_, 2, v_v_2443_);
lean_ctor_set(v___x_2450_, 1, v_k_2442_);
lean_ctor_set(v___x_2450_, 0, v___x_2453_);
v___x_2455_ = v___x_2450_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2453_);
lean_ctor_set(v_reuseFailAlloc_2462_, 1, v_k_2442_);
lean_ctor_set(v_reuseFailAlloc_2462_, 2, v_v_2443_);
lean_ctor_set(v_reuseFailAlloc_2462_, 3, v_l_2403_);
lean_ctor_set(v_reuseFailAlloc_2462_, 4, v_l_2403_);
v___x_2455_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
lean_object* v___x_2457_; 
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 4, v_l_2403_);
lean_ctor_set(v___x_2445_, 2, v_v_2297_);
lean_ctor_set(v___x_2445_, 1, v_k_2296_);
lean_ctor_set(v___x_2445_, 0, v___x_2453_);
v___x_2457_ = v___x_2445_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2453_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2461_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2461_, 3, v_l_2403_);
lean_ctor_set(v_reuseFailAlloc_2461_, 4, v_l_2403_);
v___x_2457_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2459_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v___x_2457_);
lean_ctor_set(v___x_2301_, 3, v___x_2455_);
lean_ctor_set(v___x_2301_, 2, v_v_2448_);
lean_ctor_set(v___x_2301_, 1, v_k_2447_);
lean_ctor_set(v___x_2301_, 0, v___x_2452_);
v___x_2459_ = v___x_2301_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2452_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v_k_2447_);
lean_ctor_set(v_reuseFailAlloc_2460_, 2, v_v_2448_);
lean_ctor_set(v_reuseFailAlloc_2460_, 3, v___x_2455_);
lean_ctor_set(v_reuseFailAlloc_2460_, 4, v___x_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
}
}
else
{
lean_object* v___x_2471_; lean_object* v___x_2473_; 
v___x_2471_ = lean_unsigned_to_nat(2u);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v_r_2441_);
lean_ctor_set(v___x_2301_, 3, v___x_2304_);
lean_ctor_set(v___x_2301_, 0, v___x_2471_);
v___x_2473_ = v___x_2301_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2471_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2474_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2474_, 3, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2474_, 4, v_r_2441_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
else
{
lean_object* v___x_2475_; lean_object* v___x_2477_; 
v___x_2475_ = lean_unsigned_to_nat(1u);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v___x_2304_);
lean_ctor_set(v___x_2301_, 3, v___x_2304_);
lean_ctor_set(v___x_2301_, 0, v___x_2475_);
v___x_2477_ = v___x_2301_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2478_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2478_, 3, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2478_, 4, v___x_2304_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
case 1:
{
lean_object* v___x_2480_; 
lean_dec(v_v_2297_);
lean_dec(v_k_2296_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 2, v_v_2293_);
lean_ctor_set(v___x_2301_, 1, v_k_2292_);
v___x_2480_ = v___x_2301_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_size_2295_);
lean_ctor_set(v_reuseFailAlloc_2481_, 1, v_k_2292_);
lean_ctor_set(v_reuseFailAlloc_2481_, 2, v_v_2293_);
lean_ctor_set(v_reuseFailAlloc_2481_, 3, v_l_2298_);
lean_ctor_set(v_reuseFailAlloc_2481_, 4, v_r_2299_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
default: 
{
lean_object* v___x_2482_; 
lean_dec(v_size_2295_);
v___x_2482_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg(v_k_2292_, v_v_2293_, v_r_2299_);
if (lean_obj_tag(v_l_2298_) == 0)
{
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_size_2483_; lean_object* v_size_2484_; lean_object* v_k_2485_; lean_object* v_v_2486_; lean_object* v_l_2487_; lean_object* v_r_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; uint8_t v___x_2491_; 
v_size_2483_ = lean_ctor_get(v_l_2298_, 0);
v_size_2484_ = lean_ctor_get(v___x_2482_, 0);
v_k_2485_ = lean_ctor_get(v___x_2482_, 1);
v_v_2486_ = lean_ctor_get(v___x_2482_, 2);
v_l_2487_ = lean_ctor_get(v___x_2482_, 3);
lean_inc(v_l_2487_);
v_r_2488_ = lean_ctor_get(v___x_2482_, 4);
v___x_2489_ = lean_unsigned_to_nat(3u);
v___x_2490_ = lean_nat_mul(v___x_2489_, v_size_2483_);
v___x_2491_ = lean_nat_dec_lt(v___x_2490_, v_size_2484_);
lean_dec(v___x_2490_);
if (v___x_2491_ == 0)
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2496_; 
lean_dec(v_l_2487_);
v___x_2492_ = lean_unsigned_to_nat(1u);
v___x_2493_ = lean_nat_add(v___x_2492_, v_size_2483_);
v___x_2494_ = lean_nat_add(v___x_2493_, v_size_2484_);
lean_dec(v___x_2493_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v___x_2482_);
lean_ctor_set(v___x_2301_, 0, v___x_2494_);
v___x_2496_ = v___x_2301_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2494_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2497_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2497_, 3, v_l_2298_);
lean_ctor_set(v_reuseFailAlloc_2497_, 4, v___x_2482_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
else
{
lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2567_; 
lean_inc(v_r_2488_);
lean_inc(v_v_2486_);
lean_inc(v_k_2485_);
lean_inc(v_size_2484_);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2567_ == 0)
{
lean_object* v_unused_2568_; lean_object* v_unused_2569_; lean_object* v_unused_2570_; lean_object* v_unused_2571_; lean_object* v_unused_2572_; 
v_unused_2568_ = lean_ctor_get(v___x_2482_, 4);
lean_dec(v_unused_2568_);
v_unused_2569_ = lean_ctor_get(v___x_2482_, 3);
lean_dec(v_unused_2569_);
v_unused_2570_ = lean_ctor_get(v___x_2482_, 2);
lean_dec(v_unused_2570_);
v_unused_2571_ = lean_ctor_get(v___x_2482_, 1);
lean_dec(v_unused_2571_);
v_unused_2572_ = lean_ctor_get(v___x_2482_, 0);
lean_dec(v_unused_2572_);
v___x_2499_ = v___x_2482_;
v_isShared_2500_ = v_isSharedCheck_2567_;
goto v_resetjp_2498_;
}
else
{
lean_dec(v___x_2482_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2567_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
if (lean_obj_tag(v_l_2487_) == 0)
{
if (lean_obj_tag(v_r_2488_) == 0)
{
lean_object* v_size_2501_; lean_object* v_k_2502_; lean_object* v_v_2503_; lean_object* v_l_2504_; lean_object* v_r_2505_; lean_object* v_size_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; uint8_t v___x_2509_; 
v_size_2501_ = lean_ctor_get(v_l_2487_, 0);
v_k_2502_ = lean_ctor_get(v_l_2487_, 1);
v_v_2503_ = lean_ctor_get(v_l_2487_, 2);
v_l_2504_ = lean_ctor_get(v_l_2487_, 3);
v_r_2505_ = lean_ctor_get(v_l_2487_, 4);
v_size_2506_ = lean_ctor_get(v_r_2488_, 0);
v___x_2507_ = lean_unsigned_to_nat(2u);
v___x_2508_ = lean_nat_mul(v___x_2507_, v_size_2506_);
v___x_2509_ = lean_nat_dec_lt(v_size_2501_, v___x_2508_);
lean_dec(v___x_2508_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2538_; 
lean_inc(v_r_2505_);
lean_inc(v_l_2504_);
lean_inc(v_v_2503_);
lean_inc(v_k_2502_);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_l_2487_);
if (v_isSharedCheck_2538_ == 0)
{
lean_object* v_unused_2539_; lean_object* v_unused_2540_; lean_object* v_unused_2541_; lean_object* v_unused_2542_; lean_object* v_unused_2543_; 
v_unused_2539_ = lean_ctor_get(v_l_2487_, 4);
lean_dec(v_unused_2539_);
v_unused_2540_ = lean_ctor_get(v_l_2487_, 3);
lean_dec(v_unused_2540_);
v_unused_2541_ = lean_ctor_get(v_l_2487_, 2);
lean_dec(v_unused_2541_);
v_unused_2542_ = lean_ctor_get(v_l_2487_, 1);
lean_dec(v_unused_2542_);
v_unused_2543_ = lean_ctor_get(v_l_2487_, 0);
lean_dec(v_unused_2543_);
v___x_2511_ = v_l_2487_;
v_isShared_2512_ = v_isSharedCheck_2538_;
goto v_resetjp_2510_;
}
else
{
lean_dec(v_l_2487_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2538_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2528_; 
v___x_2513_ = lean_unsigned_to_nat(1u);
v___x_2514_ = lean_nat_add(v___x_2513_, v_size_2483_);
v___x_2515_ = lean_nat_add(v___x_2514_, v_size_2484_);
lean_dec(v_size_2484_);
if (lean_obj_tag(v_l_2504_) == 0)
{
lean_object* v_size_2536_; 
v_size_2536_ = lean_ctor_get(v_l_2504_, 0);
lean_inc(v_size_2536_);
v___y_2528_ = v_size_2536_;
goto v___jp_2527_;
}
else
{
lean_object* v___x_2537_; 
v___x_2537_ = lean_unsigned_to_nat(0u);
v___y_2528_ = v___x_2537_;
goto v___jp_2527_;
}
v___jp_2516_:
{
lean_object* v___x_2520_; lean_object* v___x_2522_; 
v___x_2520_ = lean_nat_add(v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec(v___y_2518_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 4, v_r_2488_);
lean_ctor_set(v___x_2511_, 3, v_r_2505_);
lean_ctor_set(v___x_2511_, 2, v_v_2486_);
lean_ctor_set(v___x_2511_, 1, v_k_2485_);
lean_ctor_set(v___x_2511_, 0, v___x_2520_);
v___x_2522_ = v___x_2511_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2520_);
lean_ctor_set(v_reuseFailAlloc_2526_, 1, v_k_2485_);
lean_ctor_set(v_reuseFailAlloc_2526_, 2, v_v_2486_);
lean_ctor_set(v_reuseFailAlloc_2526_, 3, v_r_2505_);
lean_ctor_set(v_reuseFailAlloc_2526_, 4, v_r_2488_);
v___x_2522_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
lean_object* v___x_2524_; 
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 4, v___x_2522_);
lean_ctor_set(v___x_2499_, 3, v___y_2517_);
lean_ctor_set(v___x_2499_, 2, v_v_2503_);
lean_ctor_set(v___x_2499_, 1, v_k_2502_);
lean_ctor_set(v___x_2499_, 0, v___x_2515_);
v___x_2524_ = v___x_2499_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2515_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v_k_2502_);
lean_ctor_set(v_reuseFailAlloc_2525_, 2, v_v_2503_);
lean_ctor_set(v_reuseFailAlloc_2525_, 3, v___y_2517_);
lean_ctor_set(v_reuseFailAlloc_2525_, 4, v___x_2522_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
v___jp_2527_:
{
lean_object* v___x_2529_; lean_object* v___x_2531_; 
v___x_2529_ = lean_nat_add(v___x_2514_, v___y_2528_);
lean_dec(v___y_2528_);
lean_dec(v___x_2514_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v_l_2504_);
lean_ctor_set(v___x_2301_, 0, v___x_2529_);
v___x_2531_ = v___x_2301_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2529_);
lean_ctor_set(v_reuseFailAlloc_2535_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2535_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2535_, 3, v_l_2298_);
lean_ctor_set(v_reuseFailAlloc_2535_, 4, v_l_2504_);
v___x_2531_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v___x_2532_; 
v___x_2532_ = lean_nat_add(v___x_2513_, v_size_2506_);
if (lean_obj_tag(v_r_2505_) == 0)
{
lean_object* v_size_2533_; 
v_size_2533_ = lean_ctor_get(v_r_2505_, 0);
lean_inc(v_size_2533_);
v___y_2517_ = v___x_2531_;
v___y_2518_ = v___x_2532_;
v___y_2519_ = v_size_2533_;
goto v___jp_2516_;
}
else
{
lean_object* v___x_2534_; 
v___x_2534_ = lean_unsigned_to_nat(0u);
v___y_2517_ = v___x_2531_;
v___y_2518_ = v___x_2532_;
v___y_2519_ = v___x_2534_;
goto v___jp_2516_;
}
}
}
}
}
else
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2549_; 
lean_del_object(v___x_2301_);
v___x_2544_ = lean_unsigned_to_nat(1u);
v___x_2545_ = lean_nat_add(v___x_2544_, v_size_2483_);
v___x_2546_ = lean_nat_add(v___x_2545_, v_size_2484_);
lean_dec(v_size_2484_);
v___x_2547_ = lean_nat_add(v___x_2545_, v_size_2501_);
lean_dec(v___x_2545_);
lean_inc_ref(v_l_2298_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 4, v_l_2487_);
lean_ctor_set(v___x_2499_, 3, v_l_2298_);
lean_ctor_set(v___x_2499_, 2, v_v_2297_);
lean_ctor_set(v___x_2499_, 1, v_k_2296_);
lean_ctor_set(v___x_2499_, 0, v___x_2547_);
v___x_2549_ = v___x_2499_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2547_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2562_, 3, v_l_2298_);
lean_ctor_set(v_reuseFailAlloc_2562_, 4, v_l_2487_);
v___x_2549_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
v_isSharedCheck_2556_ = !lean_is_exclusive(v_l_2298_);
if (v_isSharedCheck_2556_ == 0)
{
lean_object* v_unused_2557_; lean_object* v_unused_2558_; lean_object* v_unused_2559_; lean_object* v_unused_2560_; lean_object* v_unused_2561_; 
v_unused_2557_ = lean_ctor_get(v_l_2298_, 4);
lean_dec(v_unused_2557_);
v_unused_2558_ = lean_ctor_get(v_l_2298_, 3);
lean_dec(v_unused_2558_);
v_unused_2559_ = lean_ctor_get(v_l_2298_, 2);
lean_dec(v_unused_2559_);
v_unused_2560_ = lean_ctor_get(v_l_2298_, 1);
lean_dec(v_unused_2560_);
v_unused_2561_ = lean_ctor_get(v_l_2298_, 0);
lean_dec(v_unused_2561_);
v___x_2551_ = v_l_2298_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_dec(v_l_2298_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 4, v_r_2488_);
lean_ctor_set(v___x_2551_, 3, v___x_2549_);
lean_ctor_set(v___x_2551_, 2, v_v_2486_);
lean_ctor_set(v___x_2551_, 1, v_k_2485_);
lean_ctor_set(v___x_2551_, 0, v___x_2546_);
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2546_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v_k_2485_);
lean_ctor_set(v_reuseFailAlloc_2555_, 2, v_v_2486_);
lean_ctor_set(v_reuseFailAlloc_2555_, 3, v___x_2549_);
lean_ctor_set(v_reuseFailAlloc_2555_, 4, v_r_2488_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
}
else
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
lean_dec_ref_known(v_l_2487_, 5);
lean_del_object(v___x_2499_);
lean_dec(v_v_2486_);
lean_dec(v_k_2485_);
lean_dec(v_size_2484_);
lean_dec_ref_known(v_l_2298_, 5);
lean_del_object(v___x_2301_);
lean_dec(v_v_2297_);
lean_dec(v_k_2296_);
v___x_2563_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__7);
v___x_2564_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4___redArg(v___x_2563_);
return v___x_2564_;
}
}
else
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
lean_del_object(v___x_2499_);
lean_dec(v_r_2488_);
lean_dec(v_v_2486_);
lean_dec(v_k_2485_);
lean_dec(v_size_2484_);
lean_dec_ref_known(v_l_2298_, 5);
lean_del_object(v___x_2301_);
lean_dec(v_v_2297_);
lean_dec(v_k_2296_);
v___x_2565_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__8);
v___x_2566_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4___redArg(v___x_2565_);
return v___x_2566_;
}
}
}
}
else
{
lean_object* v_size_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2577_; 
v_size_2573_ = lean_ctor_get(v_l_2298_, 0);
v___x_2574_ = lean_unsigned_to_nat(1u);
v___x_2575_ = lean_nat_add(v___x_2574_, v_size_2573_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v___x_2482_);
lean_ctor_set(v___x_2301_, 0, v___x_2575_);
v___x_2577_ = v___x_2301_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2575_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2578_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2578_, 3, v_l_2298_);
lean_ctor_set(v_reuseFailAlloc_2578_, 4, v___x_2482_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
else
{
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_l_2579_; 
v_l_2579_ = lean_ctor_get(v___x_2482_, 3);
lean_inc(v_l_2579_);
if (lean_obj_tag(v_l_2579_) == 0)
{
lean_object* v_r_2580_; 
v_r_2580_ = lean_ctor_get(v___x_2482_, 4);
lean_inc(v_r_2580_);
if (lean_obj_tag(v_r_2580_) == 0)
{
lean_object* v_size_2581_; lean_object* v_k_2582_; lean_object* v_v_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2597_; 
v_size_2581_ = lean_ctor_get(v___x_2482_, 0);
v_k_2582_ = lean_ctor_get(v___x_2482_, 1);
v_v_2583_ = lean_ctor_get(v___x_2482_, 2);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2597_ == 0)
{
lean_object* v_unused_2598_; lean_object* v_unused_2599_; 
v_unused_2598_ = lean_ctor_get(v___x_2482_, 4);
lean_dec(v_unused_2598_);
v_unused_2599_ = lean_ctor_get(v___x_2482_, 3);
lean_dec(v_unused_2599_);
v___x_2585_ = v___x_2482_;
v_isShared_2586_ = v_isSharedCheck_2597_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_v_2583_);
lean_inc(v_k_2582_);
lean_inc(v_size_2581_);
lean_dec(v___x_2482_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2597_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v_size_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2592_; 
v_size_2587_ = lean_ctor_get(v_l_2579_, 0);
v___x_2588_ = lean_unsigned_to_nat(1u);
v___x_2589_ = lean_nat_add(v___x_2588_, v_size_2581_);
lean_dec(v_size_2581_);
v___x_2590_ = lean_nat_add(v___x_2588_, v_size_2587_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 4, v_l_2579_);
lean_ctor_set(v___x_2585_, 3, v_l_2298_);
lean_ctor_set(v___x_2585_, 2, v_v_2297_);
lean_ctor_set(v___x_2585_, 1, v_k_2296_);
lean_ctor_set(v___x_2585_, 0, v___x_2590_);
v___x_2592_ = v___x_2585_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2590_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2596_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2596_, 3, v_l_2298_);
lean_ctor_set(v_reuseFailAlloc_2596_, 4, v_l_2579_);
v___x_2592_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
lean_object* v___x_2594_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v_r_2580_);
lean_ctor_set(v___x_2301_, 3, v___x_2592_);
lean_ctor_set(v___x_2301_, 2, v_v_2583_);
lean_ctor_set(v___x_2301_, 1, v_k_2582_);
lean_ctor_set(v___x_2301_, 0, v___x_2589_);
v___x_2594_ = v___x_2301_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2589_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v_k_2582_);
lean_ctor_set(v_reuseFailAlloc_2595_, 2, v_v_2583_);
lean_ctor_set(v_reuseFailAlloc_2595_, 3, v___x_2592_);
lean_ctor_set(v_reuseFailAlloc_2595_, 4, v_r_2580_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
else
{
lean_object* v_k_2600_; lean_object* v_v_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2625_; 
v_k_2600_ = lean_ctor_get(v___x_2482_, 1);
v_v_2601_ = lean_ctor_get(v___x_2482_, 2);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2625_ == 0)
{
lean_object* v_unused_2626_; lean_object* v_unused_2627_; lean_object* v_unused_2628_; 
v_unused_2626_ = lean_ctor_get(v___x_2482_, 4);
lean_dec(v_unused_2626_);
v_unused_2627_ = lean_ctor_get(v___x_2482_, 3);
lean_dec(v_unused_2627_);
v_unused_2628_ = lean_ctor_get(v___x_2482_, 0);
lean_dec(v_unused_2628_);
v___x_2603_ = v___x_2482_;
v_isShared_2604_ = v_isSharedCheck_2625_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_v_2601_);
lean_inc(v_k_2600_);
lean_dec(v___x_2482_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2625_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v_k_2605_; lean_object* v_v_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2621_; 
v_k_2605_ = lean_ctor_get(v_l_2579_, 1);
v_v_2606_ = lean_ctor_get(v_l_2579_, 2);
v_isSharedCheck_2621_ = !lean_is_exclusive(v_l_2579_);
if (v_isSharedCheck_2621_ == 0)
{
lean_object* v_unused_2622_; lean_object* v_unused_2623_; lean_object* v_unused_2624_; 
v_unused_2622_ = lean_ctor_get(v_l_2579_, 4);
lean_dec(v_unused_2622_);
v_unused_2623_ = lean_ctor_get(v_l_2579_, 3);
lean_dec(v_unused_2623_);
v_unused_2624_ = lean_ctor_get(v_l_2579_, 0);
lean_dec(v_unused_2624_);
v___x_2608_ = v_l_2579_;
v_isShared_2609_ = v_isSharedCheck_2621_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_v_2606_);
lean_inc(v_k_2605_);
lean_dec(v_l_2579_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2621_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2613_; 
v___x_2610_ = lean_unsigned_to_nat(3u);
v___x_2611_ = lean_unsigned_to_nat(1u);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 4, v_r_2580_);
lean_ctor_set(v___x_2608_, 3, v_r_2580_);
lean_ctor_set(v___x_2608_, 2, v_v_2297_);
lean_ctor_set(v___x_2608_, 1, v_k_2296_);
lean_ctor_set(v___x_2608_, 0, v___x_2611_);
v___x_2613_ = v___x_2608_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2611_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2620_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2620_, 3, v_r_2580_);
lean_ctor_set(v_reuseFailAlloc_2620_, 4, v_r_2580_);
v___x_2613_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
lean_object* v___x_2615_; 
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 3, v_r_2580_);
lean_ctor_set(v___x_2603_, 0, v___x_2611_);
v___x_2615_ = v___x_2603_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2611_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_k_2600_);
lean_ctor_set(v_reuseFailAlloc_2619_, 2, v_v_2601_);
lean_ctor_set(v_reuseFailAlloc_2619_, 3, v_r_2580_);
lean_ctor_set(v_reuseFailAlloc_2619_, 4, v_r_2580_);
v___x_2615_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
lean_object* v___x_2617_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v___x_2615_);
lean_ctor_set(v___x_2301_, 3, v___x_2613_);
lean_ctor_set(v___x_2301_, 2, v_v_2606_);
lean_ctor_set(v___x_2301_, 1, v_k_2605_);
lean_ctor_set(v___x_2301_, 0, v___x_2610_);
v___x_2617_ = v___x_2301_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2610_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v_k_2605_);
lean_ctor_set(v_reuseFailAlloc_2618_, 2, v_v_2606_);
lean_ctor_set(v_reuseFailAlloc_2618_, 3, v___x_2613_);
lean_ctor_set(v_reuseFailAlloc_2618_, 4, v___x_2615_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_2629_; 
v_r_2629_ = lean_ctor_get(v___x_2482_, 4);
lean_inc(v_r_2629_);
if (lean_obj_tag(v_r_2629_) == 0)
{
lean_object* v_k_2630_; lean_object* v_v_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2643_; 
v_k_2630_ = lean_ctor_get(v___x_2482_, 1);
v_v_2631_ = lean_ctor_get(v___x_2482_, 2);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2643_ == 0)
{
lean_object* v_unused_2644_; lean_object* v_unused_2645_; lean_object* v_unused_2646_; 
v_unused_2644_ = lean_ctor_get(v___x_2482_, 4);
lean_dec(v_unused_2644_);
v_unused_2645_ = lean_ctor_get(v___x_2482_, 3);
lean_dec(v_unused_2645_);
v_unused_2646_ = lean_ctor_get(v___x_2482_, 0);
lean_dec(v_unused_2646_);
v___x_2633_ = v___x_2482_;
v_isShared_2634_ = v_isSharedCheck_2643_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_v_2631_);
lean_inc(v_k_2630_);
lean_dec(v___x_2482_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2643_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2638_; 
v___x_2635_ = lean_unsigned_to_nat(3u);
v___x_2636_ = lean_unsigned_to_nat(1u);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 4, v_l_2579_);
lean_ctor_set(v___x_2633_, 2, v_v_2297_);
lean_ctor_set(v___x_2633_, 1, v_k_2296_);
lean_ctor_set(v___x_2633_, 0, v___x_2636_);
v___x_2638_ = v___x_2633_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2636_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2642_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2642_, 3, v_l_2579_);
lean_ctor_set(v_reuseFailAlloc_2642_, 4, v_l_2579_);
v___x_2638_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
lean_object* v___x_2640_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v_r_2629_);
lean_ctor_set(v___x_2301_, 3, v___x_2638_);
lean_ctor_set(v___x_2301_, 2, v_v_2631_);
lean_ctor_set(v___x_2301_, 1, v_k_2630_);
lean_ctor_set(v___x_2301_, 0, v___x_2635_);
v___x_2640_ = v___x_2301_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2635_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v_k_2630_);
lean_ctor_set(v_reuseFailAlloc_2641_, 2, v_v_2631_);
lean_ctor_set(v_reuseFailAlloc_2641_, 3, v___x_2638_);
lean_ctor_set(v_reuseFailAlloc_2641_, 4, v_r_2629_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
else
{
lean_object* v___x_2647_; lean_object* v___x_2649_; 
v___x_2647_ = lean_unsigned_to_nat(2u);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v___x_2482_);
lean_ctor_set(v___x_2301_, 3, v_r_2629_);
lean_ctor_set(v___x_2301_, 0, v___x_2647_);
v___x_2649_ = v___x_2301_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2647_);
lean_ctor_set(v_reuseFailAlloc_2650_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2650_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2650_, 3, v_r_2629_);
lean_ctor_set(v_reuseFailAlloc_2650_, 4, v___x_2482_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
else
{
lean_object* v___x_2651_; lean_object* v___x_2653_; 
v___x_2651_ = lean_unsigned_to_nat(1u);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v___x_2482_);
lean_ctor_set(v___x_2301_, 3, v___x_2482_);
lean_ctor_set(v___x_2301_, 0, v___x_2651_);
v___x_2653_ = v___x_2301_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2651_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v_k_2296_);
lean_ctor_set(v_reuseFailAlloc_2654_, 2, v_v_2297_);
lean_ctor_set(v_reuseFailAlloc_2654_, 3, v___x_2482_);
lean_ctor_set(v_reuseFailAlloc_2654_, 4, v___x_2482_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = lean_unsigned_to_nat(1u);
v___x_2657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2656_);
lean_ctor_set(v___x_2657_, 1, v_k_2292_);
lean_ctor_set(v___x_2657_, 2, v_v_2293_);
lean_ctor_set(v___x_2657_, 3, v_t_2294_);
lean_ctor_set(v___x_2657_, 4, v_t_2294_);
return v___x_2657_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__3_spec__6(lean_object* v_init_2658_, lean_object* v_x_2659_){
_start:
{
if (lean_obj_tag(v_x_2659_) == 0)
{
lean_object* v_k_2660_; lean_object* v_v_2661_; lean_object* v_l_2662_; lean_object* v_r_2663_; lean_object* v___x_2664_; uint8_t v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v_k_2660_ = lean_ctor_get(v_x_2659_, 1);
lean_inc(v_k_2660_);
v_v_2661_ = lean_ctor_get(v_x_2659_, 2);
lean_inc(v_v_2661_);
v_l_2662_ = lean_ctor_get(v_x_2659_, 3);
lean_inc(v_l_2662_);
v_r_2663_ = lean_ctor_get(v_x_2659_, 4);
lean_inc(v_r_2663_);
lean_dec_ref_known(v_x_2659_, 5);
v___x_2664_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__3_spec__6(v_init_2658_, v_l_2662_);
v___x_2665_ = 1;
v___x_2666_ = l_Lean_Name_toString(v_k_2660_, v___x_2665_);
v___x_2667_ = l_Lean_Array_toJson___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1(v_v_2661_);
v___x_2668_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg(v___x_2666_, v___x_2667_, v___x_2664_);
v_init_2658_ = v___x_2668_;
v_x_2659_ = v_r_2663_;
goto _start;
}
else
{
return v_init_2658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1(lean_object* v_m_2670_){
_start:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2671_ = lean_box(1);
v___x_2672_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__3_spec__6(v___x_2671_, v_m_2670_);
v___x_2673_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2672_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonModuleSetup_toJson_spec__0(lean_object* v_k_2674_, lean_object* v_x_2675_){
_start:
{
if (lean_obj_tag(v_x_2675_) == 0)
{
lean_object* v___x_2676_; 
lean_dec_ref(v_k_2674_);
v___x_2676_ = lean_box(0);
return v___x_2676_;
}
else
{
lean_object* v_val_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v_val_2677_ = lean_ctor_get(v_x_2675_, 0);
lean_inc(v_val_2677_);
lean_dec_ref_known(v_x_2675_, 1);
v___x_2678_ = l_Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0(v_val_2677_);
v___x_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2679_, 0, v_k_2674_);
lean_ctor_set(v___x_2679_, 1, v___x_2678_);
v___x_2680_ = lean_box(0);
v___x_2681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2679_);
lean_ctor_set(v___x_2681_, 1, v___x_2680_);
return v___x_2681_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__9_spec__13(lean_object* v_init_2682_, lean_object* v_x_2683_){
_start:
{
if (lean_obj_tag(v_x_2683_) == 0)
{
lean_object* v_k_2684_; lean_object* v_v_2685_; lean_object* v_l_2686_; lean_object* v_r_2687_; lean_object* v___x_2688_; uint8_t v___x_2689_; lean_object* v___x_2690_; lean_object* v___y_2692_; 
v_k_2684_ = lean_ctor_get(v_x_2683_, 1);
lean_inc(v_k_2684_);
v_v_2685_ = lean_ctor_get(v_x_2683_, 2);
lean_inc(v_v_2685_);
v_l_2686_ = lean_ctor_get(v_x_2683_, 3);
lean_inc(v_l_2686_);
v_r_2687_ = lean_ctor_get(v_x_2683_, 4);
lean_inc(v_r_2687_);
lean_dec_ref_known(v_x_2683_, 5);
v___x_2688_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__9_spec__13(v_init_2682_, v_l_2686_);
v___x_2689_ = 1;
v___x_2690_ = l_Lean_Name_toString(v_k_2684_, v___x_2689_);
switch(lean_obj_tag(v_v_2685_))
{
case 0:
{
lean_object* v_s_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
v_s_2695_ = lean_ctor_get(v_v_2685_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v_v_2685_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v_v_2685_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_s_2695_);
lean_dec(v_v_2685_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
lean_ctor_set_tag(v___x_2697_, 3);
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_s_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
v___y_2692_ = v___x_2700_;
goto v___jp_2691_;
}
}
}
case 1:
{
uint8_t v_b_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
v_b_2703_ = lean_ctor_get_uint8(v_v_2685_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_v_2685_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v_v_2685_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_dec(v_v_2685_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2709_, 0, v_b_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
v___y_2692_ = v___x_2708_;
goto v___jp_2691_;
}
}
}
default: 
{
lean_object* v_n_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2719_; 
v_n_2711_ = lean_ctor_get(v_v_2685_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v_v_2685_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2713_ = v_v_2685_;
v_isShared_2714_ = v_isSharedCheck_2719_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_n_2711_);
lean_dec(v_v_2685_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2719_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2715_; lean_object* v___x_2717_; 
v___x_2715_ = l_Lean_JsonNumber_fromNat(v_n_2711_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 0, v___x_2715_);
v___x_2717_ = v___x_2713_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v___x_2715_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
v___y_2692_ = v___x_2717_;
goto v___jp_2691_;
}
}
}
}
v___jp_2691_:
{
lean_object* v___x_2693_; 
v___x_2693_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg(v___x_2690_, v___y_2692_, v___x_2688_);
v_init_2682_ = v___x_2693_;
v_x_2683_ = v_r_2687_;
goto _start;
}
}
else
{
return v_init_2682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4(lean_object* v_m_2720_){
_start:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2721_ = lean_box(1);
v___x_2722_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__9_spec__13(v___x_2721_, v_m_2720_);
v___x_2723_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__7(size_t v_sz_2724_, size_t v_i_2725_, lean_object* v_bs_2726_){
_start:
{
uint8_t v___x_2727_; 
v___x_2727_ = lean_usize_dec_lt(v_i_2725_, v_sz_2724_);
if (v___x_2727_ == 0)
{
return v_bs_2726_;
}
else
{
lean_object* v_v_2728_; lean_object* v___x_2729_; lean_object* v_bs_x27_2730_; lean_object* v___x_2731_; size_t v___x_2732_; size_t v___x_2733_; lean_object* v___x_2734_; 
v_v_2728_ = lean_array_uget(v_bs_2726_, v_i_2725_);
v___x_2729_ = lean_unsigned_to_nat(0u);
v_bs_x27_2730_ = lean_array_uset(v_bs_2726_, v_i_2725_, v___x_2729_);
v___x_2731_ = l_Lean_instToJsonPlugin_toJson(v_v_2728_);
v___x_2732_ = ((size_t)1ULL);
v___x_2733_ = lean_usize_add(v_i_2725_, v___x_2732_);
v___x_2734_ = lean_array_uset(v_bs_x27_2730_, v_i_2725_, v___x_2731_);
v_i_2725_ = v___x_2733_;
v_bs_2726_ = v___x_2734_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__7___boxed(lean_object* v_sz_2736_, lean_object* v_i_2737_, lean_object* v_bs_2738_){
_start:
{
size_t v_sz_boxed_2739_; size_t v_i_boxed_2740_; lean_object* v_res_2741_; 
v_sz_boxed_2739_ = lean_unbox_usize(v_sz_2736_);
lean_dec(v_sz_2736_);
v_i_boxed_2740_ = lean_unbox_usize(v_i_2737_);
lean_dec(v_i_2737_);
v_res_2741_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__7(v_sz_boxed_2739_, v_i_boxed_2740_, v_bs_2738_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3(lean_object* v_a_2742_){
_start:
{
size_t v_sz_2743_; size_t v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v_sz_2743_ = lean_array_size(v_a_2742_);
v___x_2744_ = ((size_t)0ULL);
v___x_2745_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__7(v_sz_2743_, v___x_2744_, v_a_2742_);
v___x_2746_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2745_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonModuleSetup_toJson(lean_object* v_x_2748_){
_start:
{
lean_object* v_name_2749_; lean_object* v_package_x3f_2750_; uint8_t v_isModule_2751_; lean_object* v_imports_x3f_2752_; lean_object* v_importArts_2753_; lean_object* v_dynlibs_2754_; lean_object* v_plugins_2755_; lean_object* v_options_2756_; lean_object* v___x_2757_; uint8_t v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v_name_2749_ = lean_ctor_get(v_x_2748_, 0);
lean_inc(v_name_2749_);
v_package_x3f_2750_ = lean_ctor_get(v_x_2748_, 1);
lean_inc(v_package_x3f_2750_);
v_isModule_2751_ = lean_ctor_get_uint8(v_x_2748_, sizeof(void*)*7);
v_imports_x3f_2752_ = lean_ctor_get(v_x_2748_, 2);
lean_inc(v_imports_x3f_2752_);
v_importArts_2753_ = lean_ctor_get(v_x_2748_, 3);
lean_inc(v_importArts_2753_);
v_dynlibs_2754_ = lean_ctor_get(v_x_2748_, 4);
lean_inc_ref(v_dynlibs_2754_);
v_plugins_2755_ = lean_ctor_get(v_x_2748_, 5);
lean_inc_ref(v_plugins_2755_);
v_options_2756_ = lean_ctor_get(v_x_2748_, 6);
lean_inc(v_options_2756_);
lean_dec_ref(v_x_2748_);
v___x_2757_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__0));
v___x_2758_ = 1;
v___x_2759_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2749_, v___x_2758_);
v___x_2760_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2759_);
v___x_2761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2757_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
v___x_2762_ = lean_box(0);
v___x_2763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2761_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = ((lean_object*)(l_Lean_instToJsonModuleSetup_toJson___closed__0));
v___x_2765_ = l_Lean_Json_opt___at___00Lean_instToJsonPlugin_toJson_spec__0(v___x_2764_, v_package_x3f_2750_);
v___x_2766_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__5));
v___x_2767_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2767_, 0, v_isModule_2751_);
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2766_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
v___x_2769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2768_);
lean_ctor_set(v___x_2769_, 1, v___x_2762_);
v___x_2770_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__0));
v___x_2771_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleSetup_toJson_spec__0(v___x_2770_, v_imports_x3f_2752_);
v___x_2772_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__8));
v___x_2773_ = l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1(v_importArts_2753_);
v___x_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2772_);
lean_ctor_set(v___x_2774_, 1, v___x_2773_);
v___x_2775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
lean_ctor_set(v___x_2775_, 1, v___x_2762_);
v___x_2776_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__12));
v___x_2777_ = l_Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2(v_dynlibs_2754_);
v___x_2778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2776_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
v___x_2779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2778_);
lean_ctor_set(v___x_2779_, 1, v___x_2762_);
v___x_2780_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__14));
v___x_2781_ = l_Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3(v_plugins_2755_);
v___x_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2780_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
v___x_2783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
lean_ctor_set(v___x_2783_, 1, v___x_2762_);
v___x_2784_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__16));
v___x_2785_ = l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4(v_options_2756_);
v___x_2786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2784_);
lean_ctor_set(v___x_2786_, 1, v___x_2785_);
v___x_2787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
lean_ctor_set(v___x_2787_, 1, v___x_2762_);
v___x_2788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2787_);
lean_ctor_set(v___x_2788_, 1, v___x_2762_);
v___x_2789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2783_);
lean_ctor_set(v___x_2789_, 1, v___x_2788_);
v___x_2790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2779_);
lean_ctor_set(v___x_2790_, 1, v___x_2789_);
v___x_2791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2775_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
v___x_2792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2771_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
v___x_2793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2769_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2765_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
v___x_2795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2763_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = ((lean_object*)(l_Lean_instToJsonImport_toJson___closed__0));
v___x_2797_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(v___x_2795_, v___x_2796_);
v___x_2798_ = l_Lean_Json_mkObj(v___x_2797_);
lean_dec(v___x_2797_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2799_, lean_object* v_msg_2800_){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4___redArg(v_msg_2800_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2(lean_object* v_00_u03b2_2802_, lean_object* v_k_2803_, lean_object* v_v_2804_, lean_object* v_t_2805_){
_start:
{
lean_object* v___x_2806_; 
v___x_2806_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg(v_k_2803_, v_v_2804_, v_t_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__3(lean_object* v_init_2807_, lean_object* v_t_2808_){
_start:
{
lean_object* v___x_2809_; 
v___x_2809_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__3_spec__6(v_init_2807_, v_t_2808_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__9(lean_object* v_init_2810_, lean_object* v_t_2811_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__9_spec__13(v_init_2810_, v_t_2811_);
return v___x_2812_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3(void){
_start:
{
lean_object* v_natZero_2819_; lean_object* v_intZero_2820_; 
v_natZero_2819_ = lean_unsigned_to_nat(0u);
v_intZero_2820_ = lean_nat_to_int(v_natZero_2819_);
return v_intZero_2820_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13(lean_object* v_init_2822_, lean_object* v_x_2823_){
_start:
{
if (lean_obj_tag(v_x_2823_) == 0)
{
lean_object* v_k_2828_; lean_object* v_v_2829_; lean_object* v_l_2830_; lean_object* v_r_2831_; lean_object* v___x_2832_; 
v_k_2828_ = lean_ctor_get(v_x_2823_, 1);
lean_inc(v_k_2828_);
v_v_2829_ = lean_ctor_get(v_x_2823_, 2);
lean_inc(v_v_2829_);
v_l_2830_ = lean_ctor_get(v_x_2823_, 3);
lean_inc(v_l_2830_);
v_r_2831_ = lean_ctor_get(v_x_2823_, 4);
lean_inc(v_r_2831_);
lean_dec_ref_known(v_x_2823_, 5);
v___x_2832_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13(v_init_2822_, v_l_2830_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_dec(v_r_2831_);
lean_dec(v_v_2829_);
lean_dec(v_k_2828_);
return v___x_2832_;
}
else
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2919_; 
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2835_ = v___x_2832_;
v_isShared_2836_ = v_isSharedCheck_2919_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2832_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2919_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v_a_2838_; lean_object* v___x_2842_; uint8_t v___x_2843_; 
v___x_2842_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__2));
v___x_2843_ = lean_string_dec_eq(v_k_2828_, v___x_2842_);
if (v___x_2843_ == 0)
{
lean_object* v_n_2844_; lean_object* v_a_2846_; uint8_t v___x_2849_; 
lean_inc(v_k_2828_);
v_n_2844_ = l_String_toName(v_k_2828_);
v___x_2849_ = l_Lean_Name_isAnonymous(v_n_2844_);
if (v___x_2849_ == 0)
{
lean_del_object(v___x_2835_);
lean_dec(v_k_2828_);
switch(lean_obj_tag(v_v_2829_))
{
case 3:
{
lean_object* v_s_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
v_s_2850_ = lean_ctor_get(v_v_2829_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v_v_2829_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v_v_2829_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_s_2850_);
lean_dec(v_v_2829_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
lean_ctor_set_tag(v___x_2852_, 0);
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_s_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
v_a_2846_ = v___x_2855_;
goto v___jp_2845_;
}
}
}
case 1:
{
uint8_t v_b_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
v_b_2858_ = lean_ctor_get_uint8(v_v_2829_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v_v_2829_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v_v_2829_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_dec(v_v_2829_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2864_, 0, v_b_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
v_a_2846_ = v___x_2863_;
goto v___jp_2845_;
}
}
}
case 2:
{
lean_object* v_n_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2880_; 
v_n_2866_ = lean_ctor_get(v_v_2829_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v_v_2829_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2868_ = v_v_2829_;
v_isShared_2869_ = v_isSharedCheck_2880_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_n_2866_);
lean_dec(v_v_2829_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2880_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v_mantissa_2870_; lean_object* v_exponent_2871_; lean_object* v_natZero_2872_; lean_object* v_intZero_2873_; uint8_t v_isNeg_2874_; 
v_mantissa_2870_ = lean_ctor_get(v_n_2866_, 0);
lean_inc(v_mantissa_2870_);
v_exponent_2871_ = lean_ctor_get(v_n_2866_, 1);
lean_inc(v_exponent_2871_);
lean_dec_ref(v_n_2866_);
v_natZero_2872_ = lean_unsigned_to_nat(0u);
v_intZero_2873_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3);
v_isNeg_2874_ = lean_int_dec_lt(v_mantissa_2870_, v_intZero_2873_);
if (v_isNeg_2874_ == 0)
{
uint8_t v___x_2875_; 
v___x_2875_ = lean_nat_dec_eq(v_exponent_2871_, v_natZero_2872_);
lean_dec(v_exponent_2871_);
if (v___x_2875_ == 0)
{
lean_dec(v_mantissa_2870_);
lean_del_object(v___x_2868_);
lean_dec(v_n_2844_);
lean_dec(v_a_2833_);
lean_dec(v_r_2831_);
goto v___jp_2826_;
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; 
v_a_2876_ = lean_nat_abs(v_mantissa_2870_);
lean_dec(v_mantissa_2870_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v_a_2876_);
v___x_2878_ = v___x_2868_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2876_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
v_a_2846_ = v___x_2878_;
goto v___jp_2845_;
}
}
}
else
{
lean_dec(v_exponent_2871_);
lean_dec(v_mantissa_2870_);
lean_del_object(v___x_2868_);
lean_dec(v_n_2844_);
lean_dec(v_a_2833_);
lean_dec(v_r_2831_);
goto v___jp_2826_;
}
}
}
default: 
{
lean_dec(v_n_2844_);
lean_dec(v_a_2833_);
lean_dec(v_r_2831_);
lean_dec(v_v_2829_);
goto v___jp_2826_;
}
}
}
else
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2886_; 
lean_dec(v_n_2844_);
lean_dec(v_a_2833_);
lean_dec(v_r_2831_);
lean_dec(v_v_2829_);
v___x_2881_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__4));
v___x_2882_ = lean_string_append(v___x_2881_, v_k_2828_);
lean_dec(v_k_2828_);
v___x_2883_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_2884_ = lean_string_append(v___x_2882_, v___x_2883_);
if (v_isShared_2836_ == 0)
{
lean_ctor_set_tag(v___x_2835_, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2884_);
v___x_2886_ = v___x_2835_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2884_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
v___jp_2845_:
{
lean_object* v___x_2847_; 
v___x_2847_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_2844_, v_a_2846_, v_a_2833_);
v_init_2822_ = v___x_2847_;
v_x_2823_ = v_r_2831_;
goto _start;
}
}
else
{
lean_del_object(v___x_2835_);
lean_dec(v_k_2828_);
switch(lean_obj_tag(v_v_2829_))
{
case 3:
{
lean_object* v_s_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
v_s_2888_ = lean_ctor_get(v_v_2829_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v_v_2829_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v_v_2829_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_s_2888_);
lean_dec(v_v_2829_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
lean_ctor_set_tag(v___x_2890_, 0);
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_s_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
v_a_2838_ = v___x_2893_;
goto v___jp_2837_;
}
}
}
case 1:
{
uint8_t v_b_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
v_b_2896_ = lean_ctor_get_uint8(v_v_2829_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_v_2829_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v_v_2829_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_dec(v_v_2829_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2902_, 0, v_b_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
v_a_2838_ = v___x_2901_;
goto v___jp_2837_;
}
}
}
case 2:
{
lean_object* v_n_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2918_; 
v_n_2904_ = lean_ctor_get(v_v_2829_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v_v_2829_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2906_ = v_v_2829_;
v_isShared_2907_ = v_isSharedCheck_2918_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_n_2904_);
lean_dec(v_v_2829_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2918_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v_mantissa_2908_; lean_object* v_exponent_2909_; lean_object* v_natZero_2910_; lean_object* v_intZero_2911_; uint8_t v_isNeg_2912_; 
v_mantissa_2908_ = lean_ctor_get(v_n_2904_, 0);
lean_inc(v_mantissa_2908_);
v_exponent_2909_ = lean_ctor_get(v_n_2904_, 1);
lean_inc(v_exponent_2909_);
lean_dec_ref(v_n_2904_);
v_natZero_2910_ = lean_unsigned_to_nat(0u);
v_intZero_2911_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3);
v_isNeg_2912_ = lean_int_dec_lt(v_mantissa_2908_, v_intZero_2911_);
if (v_isNeg_2912_ == 0)
{
uint8_t v___x_2913_; 
v___x_2913_ = lean_nat_dec_eq(v_exponent_2909_, v_natZero_2910_);
lean_dec(v_exponent_2909_);
if (v___x_2913_ == 0)
{
lean_dec(v_mantissa_2908_);
lean_del_object(v___x_2906_);
lean_dec(v_a_2833_);
lean_dec(v_r_2831_);
goto v___jp_2824_;
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; 
v_a_2914_ = lean_nat_abs(v_mantissa_2908_);
lean_dec(v_mantissa_2908_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v_a_2914_);
v___x_2916_ = v___x_2906_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2914_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
v_a_2838_ = v___x_2916_;
goto v___jp_2837_;
}
}
}
else
{
lean_dec(v_exponent_2909_);
lean_dec(v_mantissa_2908_);
lean_del_object(v___x_2906_);
lean_dec(v_a_2833_);
lean_dec(v_r_2831_);
goto v___jp_2824_;
}
}
}
default: 
{
lean_dec(v_a_2833_);
lean_dec(v_r_2831_);
lean_dec(v_v_2829_);
goto v___jp_2824_;
}
}
}
v___jp_2837_:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = lean_box(0);
v___x_2840_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2839_, v_a_2838_, v_a_2833_);
v_init_2822_ = v___x_2840_;
v_x_2823_ = v_r_2831_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_2920_; 
v___x_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2920_, 0, v_init_2822_);
return v___x_2920_;
}
v___jp_2824_:
{
lean_object* v___x_2825_; 
v___x_2825_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__1));
return v___x_2825_;
}
v___jp_2826_:
{
lean_object* v___x_2827_; 
v___x_2827_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__1));
return v___x_2827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8(lean_object* v_x_2922_){
_start:
{
if (lean_obj_tag(v_x_2922_) == 5)
{
lean_object* v_kvPairs_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v_kvPairs_2923_ = lean_ctor_get(v_x_2922_, 0);
lean_inc(v_kvPairs_2923_);
lean_dec_ref_known(v_x_2922_, 1);
v___x_2924_ = lean_box(1);
v___x_2925_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13(v___x_2924_, v_kvPairs_2923_);
return v___x_2925_;
}
else
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2926_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8___closed__0));
v___x_2927_ = lean_unsigned_to_nat(80u);
v___x_2928_ = l_Lean_Json_pretty(v_x_2922_, v___x_2927_);
v___x_2929_ = lean_string_append(v___x_2926_, v___x_2928_);
lean_dec_ref(v___x_2928_);
v___x_2930_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_2931_ = lean_string_append(v___x_2929_, v___x_2930_);
v___x_2932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2931_);
return v___x_2932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4(lean_object* v_j_2933_, lean_object* v_k_2934_){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = l_Lean_Json_getObjValD(v_j_2933_, v_k_2934_);
v___x_2936_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8(v___x_2935_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2936_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2936_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
v_a_2945_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2936_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2936_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4___boxed(lean_object* v_j_2953_, lean_object* v_k_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4(v_j_2953_, v_k_2954_);
lean_dec_ref(v_k_2954_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__10(size_t v_sz_2956_, size_t v_i_2957_, lean_object* v_bs_2958_){
_start:
{
uint8_t v___x_2959_; 
v___x_2959_ = lean_usize_dec_lt(v_i_2957_, v_sz_2956_);
if (v___x_2959_ == 0)
{
lean_object* v___x_2960_; 
v___x_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2960_, 0, v_bs_2958_);
return v___x_2960_;
}
else
{
lean_object* v_v_2961_; lean_object* v___x_2962_; 
v_v_2961_ = lean_array_uget_borrowed(v_bs_2958_, v_i_2957_);
lean_inc(v_v_2961_);
v___x_2962_ = l_Lean_Plugin_fromJson_x3f(v_v_2961_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
lean_dec_ref(v_bs_2958_);
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2962_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2962_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2972_; lean_object* v_bs_x27_2973_; size_t v___x_2974_; size_t v___x_2975_; lean_object* v___x_2976_; 
v_a_2971_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2971_);
lean_dec_ref_known(v___x_2962_, 1);
v___x_2972_ = lean_unsigned_to_nat(0u);
v_bs_x27_2973_ = lean_array_uset(v_bs_2958_, v_i_2957_, v___x_2972_);
v___x_2974_ = ((size_t)1ULL);
v___x_2975_ = lean_usize_add(v_i_2957_, v___x_2974_);
v___x_2976_ = lean_array_uset(v_bs_x27_2973_, v_i_2957_, v_a_2971_);
v_i_2957_ = v___x_2975_;
v_bs_2958_ = v___x_2976_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__10___boxed(lean_object* v_sz_2978_, lean_object* v_i_2979_, lean_object* v_bs_2980_){
_start:
{
size_t v_sz_boxed_2981_; size_t v_i_boxed_2982_; lean_object* v_res_2983_; 
v_sz_boxed_2981_ = lean_unbox_usize(v_sz_2978_);
lean_dec(v_sz_2978_);
v_i_boxed_2982_ = lean_unbox_usize(v_i_2979_);
lean_dec(v_i_2979_);
v_res_2983_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__10(v_sz_boxed_2981_, v_i_boxed_2982_, v_bs_2980_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6(lean_object* v_x_2984_){
_start:
{
if (lean_obj_tag(v_x_2984_) == 4)
{
lean_object* v_elems_2985_; size_t v_sz_2986_; size_t v___x_2987_; lean_object* v___x_2988_; 
v_elems_2985_ = lean_ctor_get(v_x_2984_, 0);
lean_inc_ref(v_elems_2985_);
lean_dec_ref_known(v_x_2984_, 1);
v_sz_2986_ = lean_array_size(v_elems_2985_);
v___x_2987_ = ((size_t)0ULL);
v___x_2988_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__10(v_sz_2986_, v___x_2987_, v_elems_2985_);
return v___x_2988_;
}
else
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2989_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0));
v___x_2990_ = lean_unsigned_to_nat(80u);
v___x_2991_ = l_Lean_Json_pretty(v_x_2984_, v___x_2990_);
v___x_2992_ = lean_string_append(v___x_2989_, v___x_2991_);
lean_dec_ref(v___x_2991_);
v___x_2993_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_2994_ = lean_string_append(v___x_2992_, v___x_2993_);
v___x_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2994_);
return v___x_2995_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3(lean_object* v_j_2996_, lean_object* v_k_2997_){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = l_Lean_Json_getObjValD(v_j_2996_, v_k_2997_);
v___x_2999_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6(v___x_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3___boxed(lean_object* v_j_3000_, lean_object* v_k_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3(v_j_3000_, v_k_3001_);
lean_dec_ref(v_k_3001_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0(lean_object* v_x_3005_){
_start:
{
if (lean_obj_tag(v_x_3005_) == 0)
{
lean_object* v___x_3006_; 
v___x_3006_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0___closed__0));
return v___x_3006_;
}
else
{
lean_object* v___x_3007_; 
v___x_3007_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0(v_x_3005_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3010_ = v___x_3007_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_3007_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
if (v_isShared_3011_ == 0)
{
v___x_3013_ = v___x_3010_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3008_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3024_; 
v_a_3016_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3018_ = v___x_3007_;
v_isShared_3019_ = v_isSharedCheck_3024_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_3007_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3024_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3020_; lean_object* v___x_3022_; 
v___x_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3020_, 0, v_a_3016_);
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 0, v___x_3020_);
v___x_3022_ = v___x_3018_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v___x_3020_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0(lean_object* v_j_3025_, lean_object* v_k_3026_){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = l_Lean_Json_getObjValD(v_j_3025_, v_k_3026_);
v___x_3028_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0(v___x_3027_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0___boxed(lean_object* v_j_3029_, lean_object* v_k_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0(v_j_3029_, v_k_3030_);
lean_dec_ref(v_k_3030_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__7(size_t v_sz_3032_, size_t v_i_3033_, lean_object* v_bs_3034_){
_start:
{
uint8_t v___x_3035_; 
v___x_3035_ = lean_usize_dec_lt(v_i_3033_, v_sz_3032_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; 
v___x_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3036_, 0, v_bs_3034_);
return v___x_3036_;
}
else
{
lean_object* v_v_3037_; lean_object* v___x_3038_; 
v_v_3037_ = lean_array_uget_borrowed(v_bs_3034_, v_i_3033_);
lean_inc(v_v_3037_);
v___x_3038_ = l_Lean_Json_getStr_x3f(v_v_3037_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
lean_dec_ref(v_bs_3034_);
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_3038_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3038_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3039_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3048_; lean_object* v_bs_x27_3049_; size_t v___x_3050_; size_t v___x_3051_; lean_object* v___x_3052_; 
v_a_3047_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_a_3047_);
lean_dec_ref_known(v___x_3038_, 1);
v___x_3048_ = lean_unsigned_to_nat(0u);
v_bs_x27_3049_ = lean_array_uset(v_bs_3034_, v_i_3033_, v___x_3048_);
v___x_3050_ = ((size_t)1ULL);
v___x_3051_ = lean_usize_add(v_i_3033_, v___x_3050_);
v___x_3052_ = lean_array_uset(v_bs_x27_3049_, v_i_3033_, v_a_3047_);
v_i_3033_ = v___x_3051_;
v_bs_3034_ = v___x_3052_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__7___boxed(lean_object* v_sz_3054_, lean_object* v_i_3055_, lean_object* v_bs_3056_){
_start:
{
size_t v_sz_boxed_3057_; size_t v_i_boxed_3058_; lean_object* v_res_3059_; 
v_sz_boxed_3057_ = lean_unbox_usize(v_sz_3054_);
lean_dec(v_sz_3054_);
v_i_boxed_3058_ = lean_unbox_usize(v_i_3055_);
lean_dec(v_i_3055_);
v_res_3059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__7(v_sz_boxed_3057_, v_i_boxed_3058_, v_bs_3056_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4(lean_object* v_x_3060_){
_start:
{
if (lean_obj_tag(v_x_3060_) == 4)
{
lean_object* v_elems_3061_; size_t v_sz_3062_; size_t v___x_3063_; lean_object* v___x_3064_; 
v_elems_3061_ = lean_ctor_get(v_x_3060_, 0);
lean_inc_ref(v_elems_3061_);
lean_dec_ref_known(v_x_3060_, 1);
v_sz_3062_ = lean_array_size(v_elems_3061_);
v___x_3063_ = ((size_t)0ULL);
v___x_3064_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__7(v_sz_3062_, v___x_3063_, v_elems_3061_);
return v___x_3064_;
}
else
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3065_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0));
v___x_3066_ = lean_unsigned_to_nat(80u);
v___x_3067_ = l_Lean_Json_pretty(v_x_3060_, v___x_3066_);
v___x_3068_ = lean_string_append(v___x_3065_, v___x_3067_);
lean_dec_ref(v___x_3067_);
v___x_3069_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_3070_ = lean_string_append(v___x_3068_, v___x_3069_);
v___x_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
return v___x_3071_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3_spec__7(size_t v_sz_3072_, size_t v_i_3073_, lean_object* v_bs_3074_){
_start:
{
uint8_t v___x_3075_; 
v___x_3075_ = lean_usize_dec_lt(v_i_3073_, v_sz_3072_);
if (v___x_3075_ == 0)
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3076_, 0, v_bs_3074_);
return v___x_3076_;
}
else
{
lean_object* v_v_3077_; lean_object* v___x_3078_; 
v_v_3077_ = lean_array_uget_borrowed(v_bs_3074_, v_i_3073_);
lean_inc(v_v_3077_);
v___x_3078_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4(v_v_3077_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec_ref(v_bs_3074_);
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_3078_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3078_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3088_; lean_object* v_bs_x27_3089_; size_t v___x_3090_; size_t v___x_3091_; lean_object* v___x_3092_; 
v_a_3087_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_a_3087_);
lean_dec_ref_known(v___x_3078_, 1);
v___x_3088_ = lean_unsigned_to_nat(0u);
v_bs_x27_3089_ = lean_array_uset(v_bs_3074_, v_i_3073_, v___x_3088_);
v___x_3090_ = ((size_t)1ULL);
v___x_3091_ = lean_usize_add(v_i_3073_, v___x_3090_);
v___x_3092_ = lean_array_uset(v_bs_x27_3089_, v_i_3073_, v_a_3087_);
v_i_3073_ = v___x_3091_;
v_bs_3074_ = v___x_3092_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3_spec__7___boxed(lean_object* v_sz_3094_, lean_object* v_i_3095_, lean_object* v_bs_3096_){
_start:
{
size_t v_sz_boxed_3097_; size_t v_i_boxed_3098_; lean_object* v_res_3099_; 
v_sz_boxed_3097_ = lean_unbox_usize(v_sz_3094_);
lean_dec(v_sz_3094_);
v_i_boxed_3098_ = lean_unbox_usize(v_i_3095_);
lean_dec(v_i_3095_);
v_res_3099_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3_spec__7(v_sz_boxed_3097_, v_i_boxed_3098_, v_bs_3096_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3(lean_object* v_x_3100_){
_start:
{
if (lean_obj_tag(v_x_3100_) == 4)
{
lean_object* v_elems_3101_; size_t v_sz_3102_; size_t v___x_3103_; lean_object* v___x_3104_; 
v_elems_3101_ = lean_ctor_get(v_x_3100_, 0);
lean_inc_ref(v_elems_3101_);
lean_dec_ref_known(v_x_3100_, 1);
v_sz_3102_ = lean_array_size(v_elems_3101_);
v___x_3103_ = ((size_t)0ULL);
v___x_3104_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3_spec__7(v_sz_3102_, v___x_3103_, v_elems_3101_);
return v___x_3104_;
}
else
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3105_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0));
v___x_3106_ = lean_unsigned_to_nat(80u);
v___x_3107_ = l_Lean_Json_pretty(v_x_3100_, v___x_3106_);
v___x_3108_ = lean_string_append(v___x_3105_, v___x_3107_);
lean_dec_ref(v___x_3107_);
v___x_3109_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_3110_ = lean_string_append(v___x_3108_, v___x_3109_);
v___x_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
return v___x_3111_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__4(lean_object* v_init_3112_, lean_object* v_x_3113_){
_start:
{
if (lean_obj_tag(v_x_3113_) == 0)
{
lean_object* v_k_3114_; lean_object* v_v_3115_; lean_object* v_l_3116_; lean_object* v_r_3117_; lean_object* v___x_3118_; 
v_k_3114_ = lean_ctor_get(v_x_3113_, 1);
lean_inc(v_k_3114_);
v_v_3115_ = lean_ctor_get(v_x_3113_, 2);
lean_inc(v_v_3115_);
v_l_3116_ = lean_ctor_get(v_x_3113_, 3);
lean_inc(v_l_3116_);
v_r_3117_ = lean_ctor_get(v_x_3113_, 4);
lean_inc(v_r_3117_);
lean_dec_ref_known(v_x_3113_, 5);
v___x_3118_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__4(v_init_3112_, v_l_3116_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_dec(v_r_3117_);
lean_dec(v_v_3115_);
lean_dec(v_k_3114_);
return v___x_3118_;
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3159_; 
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3121_ = v___x_3118_;
v_isShared_3122_ = v_isSharedCheck_3159_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3118_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3159_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3123_; uint8_t v___x_3124_; 
v___x_3123_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__2));
v___x_3124_ = lean_string_dec_eq(v_k_3114_, v___x_3123_);
if (v___x_3124_ == 0)
{
lean_object* v_n_3125_; uint8_t v___x_3126_; 
lean_inc(v_k_3114_);
v_n_3125_ = l_String_toName(v_k_3114_);
v___x_3126_ = l_Lean_Name_isAnonymous(v_n_3125_);
if (v___x_3126_ == 0)
{
lean_object* v___x_3127_; 
lean_del_object(v___x_3121_);
lean_dec(v_k_3114_);
v___x_3127_ = l_Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3(v_v_3115_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
lean_dec(v_n_3125_);
lean_dec(v_a_3119_);
lean_dec(v_r_3117_);
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3127_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3137_; 
v_a_3136_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_a_3136_);
lean_dec_ref_known(v___x_3127_, 1);
v___x_3137_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_3125_, v_a_3136_, v_a_3119_);
v_init_3112_ = v___x_3137_;
v_x_3113_ = v_r_3117_;
goto _start;
}
}
else
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3144_; 
lean_dec(v_n_3125_);
lean_dec(v_a_3119_);
lean_dec(v_r_3117_);
lean_dec(v_v_3115_);
v___x_3139_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__4));
v___x_3140_ = lean_string_append(v___x_3139_, v_k_3114_);
lean_dec(v_k_3114_);
v___x_3141_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_3142_ = lean_string_append(v___x_3140_, v___x_3141_);
if (v_isShared_3122_ == 0)
{
lean_ctor_set_tag(v___x_3121_, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3142_);
v___x_3144_ = v___x_3121_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3142_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
else
{
lean_object* v___x_3146_; 
lean_del_object(v___x_3121_);
lean_dec(v_k_3114_);
v___x_3146_ = l_Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3(v_v_3115_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_dec(v_a_3119_);
lean_dec(v_r_3117_);
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3146_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3146_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v_a_3155_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___x_3146_, 1);
v___x_3156_ = lean_box(0);
v___x_3157_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_3156_, v_a_3155_, v_a_3119_);
v_init_3112_ = v___x_3157_;
v_x_3113_ = v_r_3117_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_3160_; 
v___x_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3160_, 0, v_init_3112_);
return v___x_3160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2(lean_object* v_x_3161_){
_start:
{
if (lean_obj_tag(v_x_3161_) == 5)
{
lean_object* v_kvPairs_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v_kvPairs_3162_ = lean_ctor_get(v_x_3161_, 0);
lean_inc(v_kvPairs_3162_);
lean_dec_ref_known(v_x_3161_, 1);
v___x_3163_ = lean_box(1);
v___x_3164_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__4(v___x_3163_, v_kvPairs_3162_);
return v___x_3164_;
}
else
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3165_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8___closed__0));
v___x_3166_ = lean_unsigned_to_nat(80u);
v___x_3167_ = l_Lean_Json_pretty(v_x_3161_, v___x_3166_);
v___x_3168_ = lean_string_append(v___x_3165_, v___x_3167_);
lean_dec_ref(v___x_3167_);
v___x_3169_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_3170_ = lean_string_append(v___x_3168_, v___x_3169_);
v___x_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
return v___x_3171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1(lean_object* v_j_3172_, lean_object* v_k_3173_){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3174_ = l_Lean_Json_getObjValD(v_j_3172_, v_k_3173_);
v___x_3175_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2(v___x_3174_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1___boxed(lean_object* v_j_3176_, lean_object* v_k_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1(v_j_3176_, v_k_3177_);
lean_dec_ref(v_k_3177_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2(lean_object* v_j_3179_, lean_object* v_k_3180_){
_start:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3181_ = l_Lean_Json_getObjValD(v_j_3179_, v_k_3180_);
v___x_3182_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4(v___x_3181_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2___boxed(lean_object* v_j_3183_, lean_object* v_k_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2(v_j_3183_, v_k_3184_);
lean_dec_ref(v_k_3184_);
return v_res_3185_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3190_ = 1;
v___x_3191_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__1));
v___x_3192_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3191_, v___x_3190_);
return v___x_3192_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3193_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__4));
v___x_3194_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__2, &l_Lean_instFromJsonModuleSetup_fromJson___closed__2_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__2);
v___x_3195_ = lean_string_append(v___x_3194_, v___x_3193_);
return v___x_3195_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__5(void){
_start:
{
uint8_t v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3198_ = 1;
v___x_3199_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__4));
v___x_3200_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3199_, v___x_3198_);
return v___x_3200_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__6(void){
_start:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3201_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__5, &l_Lean_instFromJsonModuleSetup_fromJson___closed__5_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__5);
v___x_3202_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3203_ = lean_string_append(v___x_3202_, v___x_3201_);
return v___x_3203_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3204_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3205_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__6, &l_Lean_instFromJsonModuleSetup_fromJson___closed__6_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__6);
v___x_3206_ = lean_string_append(v___x_3205_, v___x_3204_);
return v___x_3206_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__9(void){
_start:
{
uint8_t v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3209_ = 1;
v___x_3210_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__8));
v___x_3211_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3210_, v___x_3209_);
return v___x_3211_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3212_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__9, &l_Lean_instFromJsonModuleSetup_fromJson___closed__9_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__9);
v___x_3213_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3214_ = lean_string_append(v___x_3213_, v___x_3212_);
return v___x_3214_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__11(void){
_start:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3215_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3216_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__10, &l_Lean_instFromJsonModuleSetup_fromJson___closed__10_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__10);
v___x_3217_ = lean_string_append(v___x_3216_, v___x_3215_);
return v___x_3217_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3218_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__9, &l_Lean_instFromJsonModuleHeader_fromJson___closed__9_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__9);
v___x_3219_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3220_ = lean_string_append(v___x_3219_, v___x_3218_);
return v___x_3220_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__13(void){
_start:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3221_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3222_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__12, &l_Lean_instFromJsonModuleSetup_fromJson___closed__12_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__12);
v___x_3223_ = lean_string_append(v___x_3222_, v___x_3221_);
return v___x_3223_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__15(void){
_start:
{
uint8_t v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3226_ = 1;
v___x_3227_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__14));
v___x_3228_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3227_, v___x_3226_);
return v___x_3228_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__16(void){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__15, &l_Lean_instFromJsonModuleSetup_fromJson___closed__15_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__15);
v___x_3230_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3231_ = lean_string_append(v___x_3230_, v___x_3229_);
return v___x_3231_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__17(void){
_start:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3232_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3233_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__16, &l_Lean_instFromJsonModuleSetup_fromJson___closed__16_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__16);
v___x_3234_ = lean_string_append(v___x_3233_, v___x_3232_);
return v___x_3234_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__19(void){
_start:
{
uint8_t v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3237_ = 1;
v___x_3238_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__18));
v___x_3239_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3238_, v___x_3237_);
return v___x_3239_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__20(void){
_start:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3240_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__19, &l_Lean_instFromJsonModuleSetup_fromJson___closed__19_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__19);
v___x_3241_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3242_ = lean_string_append(v___x_3241_, v___x_3240_);
return v___x_3242_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__21(void){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3243_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3244_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__20, &l_Lean_instFromJsonModuleSetup_fromJson___closed__20_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__20);
v___x_3245_ = lean_string_append(v___x_3244_, v___x_3243_);
return v___x_3245_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__23(void){
_start:
{
uint8_t v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3248_ = 1;
v___x_3249_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__22));
v___x_3250_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3249_, v___x_3248_);
return v___x_3250_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__24(void){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3251_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__23, &l_Lean_instFromJsonModuleSetup_fromJson___closed__23_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__23);
v___x_3252_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3253_ = lean_string_append(v___x_3252_, v___x_3251_);
return v___x_3253_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__25(void){
_start:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3254_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3255_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__24, &l_Lean_instFromJsonModuleSetup_fromJson___closed__24_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__24);
v___x_3256_ = lean_string_append(v___x_3255_, v___x_3254_);
return v___x_3256_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__27(void){
_start:
{
uint8_t v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3259_ = 1;
v___x_3260_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__26));
v___x_3261_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3260_, v___x_3259_);
return v___x_3261_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__28(void){
_start:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3262_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__27, &l_Lean_instFromJsonModuleSetup_fromJson___closed__27_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__27);
v___x_3263_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3264_ = lean_string_append(v___x_3263_, v___x_3262_);
return v___x_3264_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__29(void){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3265_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3266_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__28, &l_Lean_instFromJsonModuleSetup_fromJson___closed__28_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__28);
v___x_3267_ = lean_string_append(v___x_3266_, v___x_3265_);
return v___x_3267_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__31(void){
_start:
{
uint8_t v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3270_ = 1;
v___x_3271_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__30));
v___x_3272_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3271_, v___x_3270_);
return v___x_3272_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__32(void){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3273_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__31, &l_Lean_instFromJsonModuleSetup_fromJson___closed__31_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__31);
v___x_3274_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3275_ = lean_string_append(v___x_3274_, v___x_3273_);
return v___x_3275_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__33(void){
_start:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3276_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3277_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__32, &l_Lean_instFromJsonModuleSetup_fromJson___closed__32_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__32);
v___x_3278_ = lean_string_append(v___x_3277_, v___x_3276_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonModuleSetup_fromJson(lean_object* v_json_3279_){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3280_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__0));
lean_inc(v_json_3279_);
v___x_3281_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__0(v_json_3279_, v___x_3280_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3291_; 
lean_dec(v_json_3279_);
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3284_ = v___x_3281_;
v_isShared_3285_ = v_isSharedCheck_3291_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3281_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3291_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3289_; 
v___x_3286_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__7, &l_Lean_instFromJsonModuleSetup_fromJson___closed__7_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__7);
v___x_3287_ = lean_string_append(v___x_3286_, v_a_3282_);
lean_dec(v_a_3282_);
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 0, v___x_3287_);
v___x_3289_ = v___x_3284_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3287_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
else
{
lean_object* v_a_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v_a_3292_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_a_3292_);
lean_dec_ref_known(v___x_3281_, 1);
v___x_3293_ = ((lean_object*)(l_Lean_instToJsonModuleSetup_toJson___closed__0));
lean_inc(v_json_3279_);
v___x_3294_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1(v_json_3279_, v___x_3293_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3304_; 
lean_dec(v_a_3292_);
lean_dec(v_json_3279_);
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3297_ = v___x_3294_;
v_isShared_3298_ = v_isSharedCheck_3304_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3294_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3304_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3302_; 
v___x_3299_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__11, &l_Lean_instFromJsonModuleSetup_fromJson___closed__11_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__11);
v___x_3300_ = lean_string_append(v___x_3299_, v_a_3295_);
lean_dec(v_a_3295_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v___x_3300_);
v___x_3302_ = v___x_3297_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3300_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v_a_3305_ = lean_ctor_get(v___x_3294_, 0);
lean_inc(v_a_3305_);
lean_dec_ref_known(v___x_3294_, 1);
v___x_3306_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__5));
lean_inc(v_json_3279_);
v___x_3307_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(v_json_3279_, v___x_3306_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3317_; 
lean_dec(v_a_3305_);
lean_dec(v_a_3292_);
lean_dec(v_json_3279_);
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3310_ = v___x_3307_;
v_isShared_3311_ = v_isSharedCheck_3317_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3307_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3317_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3315_; 
v___x_3312_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__13, &l_Lean_instFromJsonModuleSetup_fromJson___closed__13_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__13);
v___x_3313_ = lean_string_append(v___x_3312_, v_a_3308_);
lean_dec(v_a_3308_);
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 0, v___x_3313_);
v___x_3315_ = v___x_3310_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
else
{
lean_object* v_a_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v_a_3318_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_a_3318_);
lean_dec_ref_known(v___x_3307_, 1);
v___x_3319_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__0));
lean_inc(v_json_3279_);
v___x_3320_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0(v_json_3279_, v___x_3319_);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3330_; 
lean_dec(v_a_3318_);
lean_dec(v_a_3305_);
lean_dec(v_a_3292_);
lean_dec(v_json_3279_);
v_a_3321_ = lean_ctor_get(v___x_3320_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3323_ = v___x_3320_;
v_isShared_3324_ = v_isSharedCheck_3330_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v___x_3320_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3330_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3328_; 
v___x_3325_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__17, &l_Lean_instFromJsonModuleSetup_fromJson___closed__17_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__17);
v___x_3326_ = lean_string_append(v___x_3325_, v_a_3321_);
lean_dec(v_a_3321_);
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 0, v___x_3326_);
v___x_3328_ = v___x_3323_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v___x_3326_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
else
{
lean_object* v_a_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v_a_3331_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_a_3331_);
lean_dec_ref_known(v___x_3320_, 1);
v___x_3332_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__8));
lean_inc(v_json_3279_);
v___x_3333_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1(v_json_3279_, v___x_3332_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3343_; 
lean_dec(v_a_3331_);
lean_dec(v_a_3318_);
lean_dec(v_a_3305_);
lean_dec(v_a_3292_);
lean_dec(v_json_3279_);
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3336_ = v___x_3333_;
v_isShared_3337_ = v_isSharedCheck_3343_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3333_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3343_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3341_; 
v___x_3338_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__21, &l_Lean_instFromJsonModuleSetup_fromJson___closed__21_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__21);
v___x_3339_ = lean_string_append(v___x_3338_, v_a_3334_);
lean_dec(v_a_3334_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v___x_3339_);
v___x_3341_ = v___x_3336_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v___x_3339_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
else
{
lean_object* v_a_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v_a_3344_ = lean_ctor_get(v___x_3333_, 0);
lean_inc(v_a_3344_);
lean_dec_ref_known(v___x_3333_, 1);
v___x_3345_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__12));
lean_inc(v_json_3279_);
v___x_3346_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2(v_json_3279_, v___x_3345_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3356_; 
lean_dec(v_a_3344_);
lean_dec(v_a_3331_);
lean_dec(v_a_3318_);
lean_dec(v_a_3305_);
lean_dec(v_a_3292_);
lean_dec(v_json_3279_);
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3349_ = v___x_3346_;
v_isShared_3350_ = v_isSharedCheck_3356_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3346_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3356_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3354_; 
v___x_3351_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__25, &l_Lean_instFromJsonModuleSetup_fromJson___closed__25_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__25);
v___x_3352_ = lean_string_append(v___x_3351_, v_a_3347_);
lean_dec(v_a_3347_);
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 0, v___x_3352_);
v___x_3354_ = v___x_3349_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3352_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
else
{
lean_object* v_a_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v_a_3357_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_a_3357_);
lean_dec_ref_known(v___x_3346_, 1);
v___x_3358_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__14));
lean_inc(v_json_3279_);
v___x_3359_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3(v_json_3279_, v___x_3358_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3369_; 
lean_dec(v_a_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3331_);
lean_dec(v_a_3318_);
lean_dec(v_a_3305_);
lean_dec(v_a_3292_);
lean_dec(v_json_3279_);
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3362_ = v___x_3359_;
v_isShared_3363_ = v_isSharedCheck_3369_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___x_3359_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3369_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3367_; 
v___x_3364_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__29, &l_Lean_instFromJsonModuleSetup_fromJson___closed__29_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__29);
v___x_3365_ = lean_string_append(v___x_3364_, v_a_3360_);
lean_dec(v_a_3360_);
if (v_isShared_3363_ == 0)
{
lean_ctor_set(v___x_3362_, 0, v___x_3365_);
v___x_3367_ = v___x_3362_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3365_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
else
{
lean_object* v_a_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v_a_3370_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_a_3370_);
lean_dec_ref_known(v___x_3359_, 1);
v___x_3371_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__16));
v___x_3372_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4(v_json_3279_, v___x_3371_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3382_; 
lean_dec(v_a_3370_);
lean_dec(v_a_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3331_);
lean_dec(v_a_3318_);
lean_dec(v_a_3305_);
lean_dec(v_a_3292_);
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3375_ = v___x_3372_;
v_isShared_3376_ = v_isSharedCheck_3382_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3372_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3382_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3380_; 
v___x_3377_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__33, &l_Lean_instFromJsonModuleSetup_fromJson___closed__33_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__33);
v___x_3378_ = lean_string_append(v___x_3377_, v_a_3373_);
lean_dec(v_a_3373_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 0, v___x_3378_);
v___x_3380_ = v___x_3375_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3378_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
else
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3392_; 
v_a_3383_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3385_ = v___x_3372_;
v_isShared_3386_ = v_isSharedCheck_3392_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3372_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3392_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3387_; uint8_t v___x_3388_; lean_object* v___x_3390_; 
v___x_3387_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3387_, 0, v_a_3292_);
lean_ctor_set(v___x_3387_, 1, v_a_3305_);
lean_ctor_set(v___x_3387_, 2, v_a_3331_);
lean_ctor_set(v___x_3387_, 3, v_a_3344_);
lean_ctor_set(v___x_3387_, 4, v_a_3357_);
lean_ctor_set(v___x_3387_, 5, v_a_3370_);
lean_ctor_set(v___x_3387_, 6, v_a_3383_);
v___x_3388_ = lean_unbox(v_a_3318_);
lean_dec(v_a_3318_);
lean_ctor_set_uint8(v___x_3387_, sizeof(void*)*7, v___x_3388_);
if (v_isShared_3386_ == 0)
{
lean_ctor_set(v___x_3385_, 0, v___x_3387_);
v___x_3390_ = v___x_3385_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3387_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
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
LEAN_EXPORT lean_object* l_Lean_ModuleSetup_load(lean_object* v_path_3396_){
_start:
{
lean_object* v___x_3398_; 
v___x_3398_ = l_IO_FS_readFile(v_path_3396_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3427_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3401_ = v___x_3398_;
v_isShared_3402_ = v_isSharedCheck_3427_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3398_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3427_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v_a_3404_; lean_object* v___x_3414_; 
v___x_3414_ = l_Lean_Json_parse(v_a_3399_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
lean_inc(v_a_3415_);
lean_dec_ref_known(v___x_3414_, 1);
v_a_3404_ = v_a_3415_;
goto v___jp_3403_;
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3417_; 
v_a_3416_ = lean_ctor_get(v___x_3414_, 0);
lean_inc(v_a_3416_);
lean_dec_ref_known(v___x_3414_, 1);
v___x_3417_ = l_Lean_instFromJsonModuleSetup_fromJson(v_a_3416_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v_a_3418_; 
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_a_3418_);
lean_dec_ref_known(v___x_3417_, 1);
v_a_3404_ = v_a_3418_;
goto v___jp_3403_;
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
lean_del_object(v___x_3401_);
v_a_3419_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3417_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3417_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
lean_ctor_set_tag(v___x_3421_, 0);
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
v___jp_3403_:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3412_; 
v___x_3405_ = ((lean_object*)(l_Lean_ModuleSetup_load___closed__0));
v___x_3406_ = lean_string_append(v___x_3405_, v_path_3396_);
v___x_3407_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3408_ = lean_string_append(v___x_3406_, v___x_3407_);
v___x_3409_ = lean_string_append(v___x_3408_, v_a_3404_);
lean_dec_ref(v_a_3404_);
v___x_3410_ = lean_mk_io_user_error(v___x_3409_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set_tag(v___x_3401_, 1);
lean_ctor_set(v___x_3401_, 0, v___x_3410_);
v___x_3412_ = v___x_3401_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3410_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
v_a_3428_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3398_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3398_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3428_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleSetup_load___boxed(lean_object* v_path_3436_, lean_object* v_a_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l_Lean_ModuleSetup_load(v_path_3436_);
lean_dec_ref(v_path_3436_);
return v_res_3438_;
}
}
lean_object* runtime_initialize_Lean_Data_Json_Parser(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_LeanOptions(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Setup(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Json_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_LeanOptions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedIRPhases_default = _init_l_Lean_instInhabitedIRPhases_default();
l_Lean_instInhabitedIRPhases = _init_l_Lean_instInhabitedIRPhases();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Setup(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Json_Parser(uint8_t builtin);
lean_object* initialize_Lean_Util_LeanOptions(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Setup(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_LeanOptions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Setup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Setup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Setup(builtin);
}
#ifdef __cplusplus
}
#endif
