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
LEAN_EXPORT lean_object* l_Lean_instCoeNameImport___lam__0(lean_object* v_x_341_){
_start:
{
uint8_t v___x_342_; uint8_t v___x_343_; lean_object* v___x_344_; 
v___x_342_ = 0;
v___x_343_ = 1;
v___x_344_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_344_, 0, v_x_341_);
lean_ctor_set_uint8(v___x_344_, sizeof(void*)*1, v___x_342_);
lean_ctor_set_uint8(v___x_344_, sizeof(void*)*1 + 1, v___x_343_);
lean_ctor_set_uint8(v___x_344_, sizeof(void*)*1 + 2, v___x_342_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringImport___lam__0(lean_object* v_imp_352_){
_start:
{
lean_object* v_module_353_; uint8_t v_importAll_354_; uint8_t v_isExported_355_; uint8_t v_isMeta_356_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_373_; 
v_module_353_ = lean_ctor_get(v_imp_352_, 0);
lean_inc(v_module_353_);
v_importAll_354_ = lean_ctor_get_uint8(v_imp_352_, sizeof(void*)*1);
v_isExported_355_ = lean_ctor_get_uint8(v_imp_352_, sizeof(void*)*1 + 1);
v_isMeta_356_ = lean_ctor_get_uint8(v_imp_352_, sizeof(void*)*1 + 2);
lean_dec_ref(v_imp_352_);
if (v_isExported_355_ == 0)
{
lean_object* v___x_376_; 
v___x_376_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__1));
v___y_373_ = v___x_376_;
goto v___jp_372_;
}
else
{
lean_object* v___x_377_; 
v___x_377_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__4));
v___y_373_ = v___x_377_;
goto v___jp_372_;
}
v___jp_357_:
{
lean_object* v___x_360_; uint8_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_360_ = lean_string_append(v___y_358_, v___y_359_);
v___x_361_ = 1;
v___x_362_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_353_, v___x_361_);
v___x_363_ = lean_string_append(v___x_360_, v___x_362_);
lean_dec_ref(v___x_362_);
return v___x_363_;
}
v___jp_364_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
lean_inc_ref(v___y_365_);
v___x_367_ = lean_string_append(v___y_365_, v___y_366_);
v___x_368_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__0));
v___x_369_ = lean_string_append(v___x_367_, v___x_368_);
if (v_importAll_354_ == 0)
{
lean_object* v___x_370_; 
v___x_370_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__1));
v___y_358_ = v___x_369_;
v___y_359_ = v___x_370_;
goto v___jp_357_;
}
else
{
lean_object* v___x_371_; 
v___x_371_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__2));
v___y_358_ = v___x_369_;
v___y_359_ = v___x_371_;
goto v___jp_357_;
}
}
v___jp_372_:
{
if (v_isMeta_356_ == 0)
{
lean_object* v___x_374_; 
v___x_374_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__1));
v___y_365_ = v___y_373_;
v___y_366_ = v___x_374_;
goto v___jp_364_;
}
else
{
lean_object* v___x_375_; 
v___x_375_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__3));
v___y_365_ = v___y_373_;
v___y_366_ = v___x_375_;
goto v___jp_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorIdx___impl(uint8_t v_x_380_){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_box(v_x_380_);
v___x_382_ = lean_obj_tag_nat(v___x_381_);
lean_dec(v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorIdx___impl___boxed(lean_object* v_x_383_){
_start:
{
uint8_t v_x_4__boxed_384_; lean_object* v_res_385_; 
v_x_4__boxed_384_ = lean_unbox(v_x_383_);
v_res_385_ = l_Lean_IRPhases_ctorIdx___impl(v_x_4__boxed_384_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorElim___redArg(lean_object* v_k_386_){
_start:
{
lean_inc(v_k_386_);
return v_k_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorElim___redArg___boxed(lean_object* v_k_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_IRPhases_ctorElim___redArg(v_k_387_);
lean_dec(v_k_387_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorElim(lean_object* v_motive_389_, lean_object* v_ctorIdx_390_, uint8_t v_t_391_, lean_object* v_h_392_, lean_object* v_k_393_){
_start:
{
lean_inc(v_k_393_);
return v_k_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorElim___boxed(lean_object* v_motive_394_, lean_object* v_ctorIdx_395_, lean_object* v_t_396_, lean_object* v_h_397_, lean_object* v_k_398_){
_start:
{
uint8_t v_t_boxed_399_; lean_object* v_res_400_; 
v_t_boxed_399_ = lean_unbox(v_t_396_);
v_res_400_ = l_Lean_IRPhases_ctorElim(v_motive_394_, v_ctorIdx_395_, v_t_boxed_399_, v_h_397_, v_k_398_);
lean_dec(v_k_398_);
lean_dec(v_ctorIdx_395_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_runtime_elim___redArg(lean_object* v_runtime_401_){
_start:
{
lean_inc(v_runtime_401_);
return v_runtime_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_runtime_elim___redArg___boxed(lean_object* v_runtime_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_IRPhases_runtime_elim___redArg(v_runtime_402_);
lean_dec(v_runtime_402_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_runtime_elim(lean_object* v_motive_404_, uint8_t v_t_405_, lean_object* v_h_406_, lean_object* v_runtime_407_){
_start:
{
lean_inc(v_runtime_407_);
return v_runtime_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_runtime_elim___boxed(lean_object* v_motive_408_, lean_object* v_t_409_, lean_object* v_h_410_, lean_object* v_runtime_411_){
_start:
{
uint8_t v_t_boxed_412_; lean_object* v_res_413_; 
v_t_boxed_412_ = lean_unbox(v_t_409_);
v_res_413_ = l_Lean_IRPhases_runtime_elim(v_motive_408_, v_t_boxed_412_, v_h_410_, v_runtime_411_);
lean_dec(v_runtime_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_comptime_elim___redArg(lean_object* v_comptime_414_){
_start:
{
lean_inc(v_comptime_414_);
return v_comptime_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_comptime_elim___redArg___boxed(lean_object* v_comptime_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_IRPhases_comptime_elim___redArg(v_comptime_415_);
lean_dec(v_comptime_415_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_comptime_elim(lean_object* v_motive_417_, uint8_t v_t_418_, lean_object* v_h_419_, lean_object* v_comptime_420_){
_start:
{
lean_inc(v_comptime_420_);
return v_comptime_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_comptime_elim___boxed(lean_object* v_motive_421_, lean_object* v_t_422_, lean_object* v_h_423_, lean_object* v_comptime_424_){
_start:
{
uint8_t v_t_boxed_425_; lean_object* v_res_426_; 
v_t_boxed_425_ = lean_unbox(v_t_422_);
v_res_426_ = l_Lean_IRPhases_comptime_elim(v_motive_421_, v_t_boxed_425_, v_h_423_, v_comptime_424_);
lean_dec(v_comptime_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_all_elim___redArg(lean_object* v_all_427_){
_start:
{
lean_inc(v_all_427_);
return v_all_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_all_elim___redArg___boxed(lean_object* v_all_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_IRPhases_all_elim___redArg(v_all_428_);
lean_dec(v_all_428_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_all_elim(lean_object* v_motive_430_, uint8_t v_t_431_, lean_object* v_h_432_, lean_object* v_all_433_){
_start:
{
lean_inc(v_all_433_);
return v_all_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_all_elim___boxed(lean_object* v_motive_434_, lean_object* v_t_435_, lean_object* v_h_436_, lean_object* v_all_437_){
_start:
{
uint8_t v_t_boxed_438_; lean_object* v_res_439_; 
v_t_boxed_438_ = lean_unbox(v_t_435_);
v_res_439_ = l_Lean_IRPhases_all_elim(v_motive_434_, v_t_boxed_438_, v_h_436_, v_all_437_);
lean_dec(v_all_437_);
return v_res_439_;
}
}
static uint8_t _init_l_Lean_instInhabitedIRPhases_default(void){
_start:
{
uint8_t v___x_440_; 
v___x_440_ = 0;
return v___x_440_;
}
}
static uint8_t _init_l_Lean_instInhabitedIRPhases(void){
_start:
{
uint8_t v___x_441_; 
v___x_441_ = 0;
return v___x_441_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqIRPhases_beq(uint8_t v_x_442_, uint8_t v_y_443_){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_444_ = lean_box(v_x_442_);
v___x_445_ = lean_obj_tag_nat(v___x_444_);
lean_dec(v___x_444_);
v___x_446_ = lean_box(v_y_443_);
v___x_447_ = lean_obj_tag_nat(v___x_446_);
lean_dec(v___x_446_);
v___x_448_ = lean_nat_dec_eq(v___x_445_, v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqIRPhases_beq___boxed(lean_object* v_x_449_, lean_object* v_y_450_){
_start:
{
uint8_t v_x_24__boxed_451_; uint8_t v_y_25__boxed_452_; uint8_t v_res_453_; lean_object* v_r_454_; 
v_x_24__boxed_451_ = lean_unbox(v_x_449_);
v_y_25__boxed_452_ = lean_unbox(v_y_450_);
v_res_453_ = l_Lean_instBEqIRPhases_beq(v_x_24__boxed_451_, v_y_25__boxed_452_);
v_r_454_ = lean_box(v_res_453_);
return v_r_454_;
}
}
static lean_object* _init_l_Lean_instReprIRPhases_repr___closed__6(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_unsigned_to_nat(2u);
v___x_467_ = lean_nat_to_int(v___x_466_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_instReprIRPhases_repr___closed__7(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = lean_nat_to_int(v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprIRPhases_repr(uint8_t v_x_470_, lean_object* v_prec_471_){
_start:
{
lean_object* v___y_473_; lean_object* v___y_480_; lean_object* v___y_487_; 
switch(v_x_470_)
{
case 0:
{
lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_493_ = lean_unsigned_to_nat(1024u);
v___x_494_ = lean_nat_dec_le(v___x_493_, v_prec_471_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; 
v___x_495_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__6, &l_Lean_instReprIRPhases_repr___closed__6_once, _init_l_Lean_instReprIRPhases_repr___closed__6);
v___y_473_ = v___x_495_;
goto v___jp_472_;
}
else
{
lean_object* v___x_496_; 
v___x_496_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__7, &l_Lean_instReprIRPhases_repr___closed__7_once, _init_l_Lean_instReprIRPhases_repr___closed__7);
v___y_473_ = v___x_496_;
goto v___jp_472_;
}
}
case 1:
{
lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_497_ = lean_unsigned_to_nat(1024u);
v___x_498_ = lean_nat_dec_le(v___x_497_, v_prec_471_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
v___x_499_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__6, &l_Lean_instReprIRPhases_repr___closed__6_once, _init_l_Lean_instReprIRPhases_repr___closed__6);
v___y_480_ = v___x_499_;
goto v___jp_479_;
}
else
{
lean_object* v___x_500_; 
v___x_500_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__7, &l_Lean_instReprIRPhases_repr___closed__7_once, _init_l_Lean_instReprIRPhases_repr___closed__7);
v___y_480_ = v___x_500_;
goto v___jp_479_;
}
}
default: 
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = lean_unsigned_to_nat(1024u);
v___x_502_ = lean_nat_dec_le(v___x_501_, v_prec_471_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
v___x_503_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__6, &l_Lean_instReprIRPhases_repr___closed__6_once, _init_l_Lean_instReprIRPhases_repr___closed__6);
v___y_487_ = v___x_503_;
goto v___jp_486_;
}
else
{
lean_object* v___x_504_; 
v___x_504_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__7, &l_Lean_instReprIRPhases_repr___closed__7_once, _init_l_Lean_instReprIRPhases_repr___closed__7);
v___y_487_ = v___x_504_;
goto v___jp_486_;
}
}
}
v___jp_472_:
{
lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_474_ = ((lean_object*)(l_Lean_instReprIRPhases_repr___closed__1));
lean_inc(v___y_473_);
v___x_475_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_475_, 0, v___y_473_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v___x_476_ = 0;
v___x_477_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set_uint8(v___x_477_, sizeof(void*)*1, v___x_476_);
v___x_478_ = l_Repr_addAppParen(v___x_477_, v_prec_471_);
return v___x_478_;
}
v___jp_479_:
{
lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_481_ = ((lean_object*)(l_Lean_instReprIRPhases_repr___closed__3));
lean_inc(v___y_480_);
v___x_482_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_482_, 0, v___y_480_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
v___x_483_ = 0;
v___x_484_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_484_, 0, v___x_482_);
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*1, v___x_483_);
v___x_485_ = l_Repr_addAppParen(v___x_484_, v_prec_471_);
return v___x_485_;
}
v___jp_486_:
{
lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_488_ = ((lean_object*)(l_Lean_instReprIRPhases_repr___closed__5));
lean_inc(v___y_487_);
v___x_489_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_489_, 0, v___y_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = 0;
v___x_491_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_491_, 0, v___x_489_);
lean_ctor_set_uint8(v___x_491_, sizeof(void*)*1, v___x_490_);
v___x_492_ = l_Repr_addAppParen(v___x_491_, v_prec_471_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprIRPhases_repr___boxed(lean_object* v_x_505_, lean_object* v_prec_506_){
_start:
{
uint8_t v_x_171__boxed_507_; lean_object* v_res_508_; 
v_x_171__boxed_507_ = lean_unbox(v_x_505_);
v_res_508_ = l_Lean_instReprIRPhases_repr(v_x_171__boxed_507_, v_prec_506_);
lean_dec(v_prec_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_511_, lean_object* v_x_512_, lean_object* v_x_513_){
_start:
{
if (lean_obj_tag(v_x_513_) == 0)
{
lean_dec(v_x_511_);
return v_x_512_;
}
else
{
lean_object* v_head_514_; lean_object* v_tail_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_525_; 
v_head_514_ = lean_ctor_get(v_x_513_, 0);
v_tail_515_ = lean_ctor_get(v_x_513_, 1);
v_isSharedCheck_525_ = !lean_is_exclusive(v_x_513_);
if (v_isSharedCheck_525_ == 0)
{
v___x_517_ = v_x_513_;
v_isShared_518_ = v_isSharedCheck_525_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_tail_515_);
lean_inc(v_head_514_);
lean_dec(v_x_513_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_525_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
lean_inc(v_x_511_);
if (v_isShared_518_ == 0)
{
lean_ctor_set_tag(v___x_517_, 5);
lean_ctor_set(v___x_517_, 1, v_x_511_);
lean_ctor_set(v___x_517_, 0, v_x_512_);
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_x_512_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_x_511_);
v___x_520_ = v_reuseFailAlloc_524_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = l_Lean_instReprImport_repr___redArg(v_head_514_);
v___x_522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v_x_512_ = v___x_522_;
v_x_513_ = v_tail_515_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0_spec__1(lean_object* v_x_526_, lean_object* v_x_527_, lean_object* v_x_528_){
_start:
{
if (lean_obj_tag(v_x_528_) == 0)
{
lean_dec(v_x_526_);
return v_x_527_;
}
else
{
lean_object* v_head_529_; lean_object* v_tail_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_540_; 
v_head_529_ = lean_ctor_get(v_x_528_, 0);
v_tail_530_ = lean_ctor_get(v_x_528_, 1);
v_isSharedCheck_540_ = !lean_is_exclusive(v_x_528_);
if (v_isSharedCheck_540_ == 0)
{
v___x_532_ = v_x_528_;
v_isShared_533_ = v_isSharedCheck_540_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_tail_530_);
lean_inc(v_head_529_);
lean_dec(v_x_528_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_540_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
lean_inc(v_x_526_);
if (v_isShared_533_ == 0)
{
lean_ctor_set_tag(v___x_532_, 5);
lean_ctor_set(v___x_532_, 1, v_x_526_);
lean_ctor_set(v___x_532_, 0, v_x_527_);
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_x_527_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_x_526_);
v___x_535_ = v_reuseFailAlloc_539_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_536_ = l_Lean_instReprImport_repr___redArg(v_head_529_);
v___x_537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0_spec__1_spec__2(v_x_526_, v___x_537_, v_tail_530_);
return v___x_538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0(lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
if (lean_obj_tag(v_x_541_) == 0)
{
lean_object* v___x_543_; 
lean_dec(v_x_542_);
v___x_543_ = lean_box(0);
return v___x_543_;
}
else
{
lean_object* v_tail_544_; 
v_tail_544_ = lean_ctor_get(v_x_541_, 1);
if (lean_obj_tag(v_tail_544_) == 0)
{
lean_object* v_head_545_; lean_object* v___x_546_; 
lean_dec(v_x_542_);
v_head_545_ = lean_ctor_get(v_x_541_, 0);
lean_inc(v_head_545_);
lean_dec_ref_known(v_x_541_, 2);
v___x_546_ = l_Lean_instReprImport_repr___redArg(v_head_545_);
return v___x_546_;
}
else
{
lean_object* v_head_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
lean_inc(v_tail_544_);
v_head_547_ = lean_ctor_get(v_x_541_, 0);
lean_inc(v_head_547_);
lean_dec_ref_known(v_x_541_, 2);
v___x_548_ = l_Lean_instReprImport_repr___redArg(v_head_547_);
v___x_549_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0_spec__1(v_x_542_, v___x_548_, v_tail_544_);
return v___x_549_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__0));
v___x_556_ = lean_string_length(v___x_555_);
return v___x_556_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_obj_once(&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3, &l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3);
v___x_558_ = lean_nat_to_int(v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0(lean_object* v_xs_566_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_567_ = lean_array_get_size(v_xs_566_);
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = lean_nat_dec_eq(v___x_567_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_570_ = lean_array_to_list(v_xs_566_);
v___x_571_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_572_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0(v___x_570_, v___x_571_);
v___x_573_ = lean_obj_once(&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4);
v___x_574_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5));
v___x_575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v___x_572_);
v___x_576_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6));
v___x_577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_573_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = l_Std_Format_fill(v___x_578_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; 
lean_dec_ref(v_xs_566_);
v___x_580_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8));
return v___x_580_;
}
}
}
static lean_object* _init_l_Lean_instReprModuleHeader_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_unsigned_to_nat(11u);
v___x_591_ = lean_nat_to_int(v___x_590_);
return v___x_591_;
}
}
static lean_object* _init_l_Lean_instReprModuleHeader_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_unsigned_to_nat(12u);
v___x_596_ = lean_nat_to_int(v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleHeader_repr___redArg(lean_object* v_x_597_){
_start:
{
lean_object* v_imports_598_; uint8_t v_isModule_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_632_; 
v_imports_598_ = lean_ctor_get(v_x_597_, 0);
v_isModule_599_ = lean_ctor_get_uint8(v_x_597_, sizeof(void*)*1);
v_isSharedCheck_632_ = !lean_is_exclusive(v_x_597_);
if (v_isSharedCheck_632_ == 0)
{
v___x_601_ = v_x_597_;
v_isShared_602_ = v_isSharedCheck_632_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_imports_598_);
lean_dec(v_x_597_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_632_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; lean_object* v___x_610_; 
v___x_603_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__5));
v___x_604_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__3));
v___x_605_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__4, &l_Lean_instReprModuleHeader_repr___redArg___closed__4_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__4);
v___x_606_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0(v_imports_598_);
v___x_607_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = 0;
if (v_isShared_602_ == 0)
{
lean_ctor_set_tag(v___x_601_, 6);
lean_ctor_set(v___x_601_, 0, v___x_607_);
v___x_610_ = v___x_601_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_607_);
v___x_610_ = v_reuseFailAlloc_631_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
lean_ctor_set_uint8(v___x_610_, sizeof(void*)*1, v___x_608_);
v___x_611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_604_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__9));
v___x_613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_611_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = lean_box(1);
v___x_615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__6));
v___x_617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set(v___x_618_, 1, v___x_603_);
v___x_619_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__7, &l_Lean_instReprModuleHeader_repr___redArg___closed__7_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__7);
v___x_620_ = l_Bool_repr___redArg(v_isModule_599_);
v___x_621_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_619_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set_uint8(v___x_622_, sizeof(void*)*1, v___x_608_);
v___x_623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_618_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__20, &l_Lean_instReprImport_repr___redArg___closed__20_once, _init_l_Lean_instReprImport_repr___redArg___closed__20);
v___x_625_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__21));
v___x_626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v___x_623_);
v___x_627_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__22));
v___x_628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_626_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_624_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v___x_630_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set_uint8(v___x_630_, sizeof(void*)*1, v___x_608_);
return v___x_630_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleHeader_repr(lean_object* v_x_633_, lean_object* v_prec_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_instReprModuleHeader_repr___redArg(v_x_633_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleHeader_repr___boxed(lean_object* v_x_636_, lean_object* v_prec_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_instReprModuleHeader_repr(v_x_636_, v_prec_637_);
lean_dec(v_prec_637_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0(size_t v_sz_648_, size_t v_i_649_, lean_object* v_bs_650_){
_start:
{
uint8_t v___x_651_; 
v___x_651_ = lean_usize_dec_lt(v_i_649_, v_sz_648_);
if (v___x_651_ == 0)
{
return v_bs_650_;
}
else
{
lean_object* v_v_652_; lean_object* v___x_653_; lean_object* v_bs_x27_654_; lean_object* v___x_655_; size_t v___x_656_; size_t v___x_657_; lean_object* v___x_658_; 
v_v_652_ = lean_array_uget(v_bs_650_, v_i_649_);
v___x_653_ = lean_unsigned_to_nat(0u);
v_bs_x27_654_ = lean_array_uset(v_bs_650_, v_i_649_, v___x_653_);
v___x_655_ = l_Lean_instToJsonImport_toJson(v_v_652_);
v___x_656_ = ((size_t)1ULL);
v___x_657_ = lean_usize_add(v_i_649_, v___x_656_);
v___x_658_ = lean_array_uset(v_bs_x27_654_, v_i_649_, v___x_655_);
v_i_649_ = v___x_657_;
v_bs_650_ = v___x_658_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0___boxed(lean_object* v_sz_660_, lean_object* v_i_661_, lean_object* v_bs_662_){
_start:
{
size_t v_sz_boxed_663_; size_t v_i_boxed_664_; lean_object* v_res_665_; 
v_sz_boxed_663_ = lean_unbox_usize(v_sz_660_);
lean_dec(v_sz_660_);
v_i_boxed_664_ = lean_unbox_usize(v_i_661_);
lean_dec(v_i_661_);
v_res_665_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0(v_sz_boxed_663_, v_i_boxed_664_, v_bs_662_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0(lean_object* v_a_666_){
_start:
{
size_t v_sz_667_; size_t v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_sz_667_ = lean_array_size(v_a_666_);
v___x_668_ = ((size_t)0ULL);
v___x_669_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0(v_sz_667_, v___x_668_, v_a_666_);
v___x_670_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonModuleHeader_toJson(lean_object* v_x_671_){
_start:
{
lean_object* v_imports_672_; uint8_t v_isModule_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_imports_672_ = lean_ctor_get(v_x_671_, 0);
lean_inc_ref(v_imports_672_);
v_isModule_673_ = lean_ctor_get_uint8(v_x_671_, sizeof(void*)*1);
lean_dec_ref(v_x_671_);
v___x_674_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__0));
v___x_675_ = l_Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0(v_imports_672_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_674_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = lean_box(0);
v___x_678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_676_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__5));
v___x_680_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_680_, 0, v_isModule_673_);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_679_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v___x_677_);
v___x_683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
lean_ctor_set(v___x_683_, 1, v___x_677_);
v___x_684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_678_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = ((lean_object*)(l_Lean_instToJsonImport_toJson___closed__0));
v___x_686_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(v___x_684_, v___x_685_);
v___x_687_ = l_Lean_Json_mkObj(v___x_686_);
lean_dec(v___x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1(size_t v_sz_690_, size_t v_i_691_, lean_object* v_bs_692_){
_start:
{
uint8_t v___x_693_; 
v___x_693_ = lean_usize_dec_lt(v_i_691_, v_sz_690_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; 
v___x_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_694_, 0, v_bs_692_);
return v___x_694_;
}
else
{
lean_object* v_v_695_; lean_object* v___x_696_; 
v_v_695_ = lean_array_uget_borrowed(v_bs_692_, v_i_691_);
lean_inc(v_v_695_);
v___x_696_ = l_Lean_instFromJsonImport_fromJson(v_v_695_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec_ref(v_bs_692_);
v_a_697_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_696_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_696_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_706_; lean_object* v_bs_x27_707_; size_t v___x_708_; size_t v___x_709_; lean_object* v___x_710_; 
v_a_705_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v___x_696_, 1);
v___x_706_ = lean_unsigned_to_nat(0u);
v_bs_x27_707_ = lean_array_uset(v_bs_692_, v_i_691_, v___x_706_);
v___x_708_ = ((size_t)1ULL);
v___x_709_ = lean_usize_add(v_i_691_, v___x_708_);
v___x_710_ = lean_array_uset(v_bs_x27_707_, v_i_691_, v_a_705_);
v_i_691_ = v___x_709_;
v_bs_692_ = v___x_710_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_712_, lean_object* v_i_713_, lean_object* v_bs_714_){
_start:
{
size_t v_sz_boxed_715_; size_t v_i_boxed_716_; lean_object* v_res_717_; 
v_sz_boxed_715_ = lean_unbox_usize(v_sz_712_);
lean_dec(v_sz_712_);
v_i_boxed_716_ = lean_unbox_usize(v_i_713_);
lean_dec(v_i_713_);
v_res_717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_715_, v_i_boxed_716_, v_bs_714_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0(lean_object* v_x_720_){
_start:
{
if (lean_obj_tag(v_x_720_) == 4)
{
lean_object* v_elems_721_; size_t v_sz_722_; size_t v___x_723_; lean_object* v___x_724_; 
v_elems_721_ = lean_ctor_get(v_x_720_, 0);
lean_inc_ref(v_elems_721_);
lean_dec_ref_known(v_x_720_, 1);
v_sz_722_ = lean_array_size(v_elems_721_);
v___x_723_ = ((size_t)0ULL);
v___x_724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1(v_sz_722_, v___x_723_, v_elems_721_);
return v___x_724_;
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_725_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0));
v___x_726_ = lean_unsigned_to_nat(80u);
v___x_727_ = l_Lean_Json_pretty(v_x_720_, v___x_726_);
v___x_728_ = lean_string_append(v___x_725_, v___x_727_);
lean_dec_ref(v___x_727_);
v___x_729_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_730_ = lean_string_append(v___x_728_, v___x_729_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0(lean_object* v_j_732_, lean_object* v_k_733_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = l_Lean_Json_getObjValD(v_j_732_, v_k_733_);
v___x_735_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0(v___x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0___boxed(lean_object* v_j_736_, lean_object* v_k_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0(v_j_736_, v_k_737_);
lean_dec_ref(v_k_737_);
return v_res_738_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__2(void){
_start:
{
uint8_t v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_743_ = 1;
v___x_744_ = ((lean_object*)(l_Lean_instFromJsonModuleHeader_fromJson___closed__1));
v___x_745_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_744_, v___x_743_);
return v___x_745_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__3(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_746_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__4));
v___x_747_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__2, &l_Lean_instFromJsonModuleHeader_fromJson___closed__2_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__2);
v___x_748_ = lean_string_append(v___x_747_, v___x_746_);
return v___x_748_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__5(void){
_start:
{
uint8_t v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_751_ = 1;
v___x_752_ = ((lean_object*)(l_Lean_instFromJsonModuleHeader_fromJson___closed__4));
v___x_753_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_752_, v___x_751_);
return v___x_753_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__6(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_754_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__5, &l_Lean_instFromJsonModuleHeader_fromJson___closed__5_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__5);
v___x_755_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__3, &l_Lean_instFromJsonModuleHeader_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__3);
v___x_756_ = lean_string_append(v___x_755_, v___x_754_);
return v___x_756_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__7(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_757_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_758_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__6, &l_Lean_instFromJsonModuleHeader_fromJson___closed__6_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__6);
v___x_759_ = lean_string_append(v___x_758_, v___x_757_);
return v___x_759_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__9(void){
_start:
{
uint8_t v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_762_ = 1;
v___x_763_ = ((lean_object*)(l_Lean_instFromJsonModuleHeader_fromJson___closed__8));
v___x_764_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_763_, v___x_762_);
return v___x_764_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__10(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_765_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__9, &l_Lean_instFromJsonModuleHeader_fromJson___closed__9_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__9);
v___x_766_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__3, &l_Lean_instFromJsonModuleHeader_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__3);
v___x_767_ = lean_string_append(v___x_766_, v___x_765_);
return v___x_767_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__11(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_769_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__10, &l_Lean_instFromJsonModuleHeader_fromJson___closed__10_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__10);
v___x_770_ = lean_string_append(v___x_769_, v___x_768_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonModuleHeader_fromJson(lean_object* v_json_771_){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__0));
lean_inc(v_json_771_);
v___x_773_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0(v_json_771_, v___x_772_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_783_; 
lean_dec(v_json_771_);
v_a_774_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_783_ == 0)
{
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_783_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_783_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_778_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__7, &l_Lean_instFromJsonModuleHeader_fromJson___closed__7_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__7);
v___x_779_ = lean_string_append(v___x_778_, v_a_774_);
lean_dec(v_a_774_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_779_);
v___x_781_ = v___x_776_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v_a_784_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_784_);
lean_dec_ref_known(v___x_773_, 1);
v___x_785_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__5));
v___x_786_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(v_json_771_, v___x_785_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_796_; 
lean_dec(v_a_784_);
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
v___x_791_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__11, &l_Lean_instFromJsonModuleHeader_fromJson___closed__11_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__11);
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
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_806_; 
v_a_797_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_806_ == 0)
{
v___x_799_ = v___x_786_;
v_isShared_800_ = v_isSharedCheck_806_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_786_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_806_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; uint8_t v___x_802_; lean_object* v___x_804_; 
v___x_801_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_801_, 0, v_a_784_);
v___x_802_ = lean_unbox(v_a_797_);
lean_dec(v_a_797_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*1, v___x_802_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_801_);
v___x_804_ = v___x_799_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_801_);
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
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0(lean_object* v___y_812_){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_813_ = lean_unsigned_to_nat(0u);
v___x_814_ = ((lean_object*)(l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_815_ = l_String_quote(v___y_812_);
v___x_816_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
v___x_817_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_814_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = l_Repr_addAppParen(v___x_817_, v___x_813_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_x_819_, lean_object* v_x_820_, lean_object* v_x_821_){
_start:
{
if (lean_obj_tag(v_x_821_) == 0)
{
lean_dec(v_x_819_);
return v_x_820_;
}
else
{
lean_object* v_head_822_; lean_object* v_tail_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_838_; 
v_head_822_ = lean_ctor_get(v_x_821_, 0);
v_tail_823_ = lean_ctor_get(v_x_821_, 1);
v_isSharedCheck_838_ = !lean_is_exclusive(v_x_821_);
if (v_isSharedCheck_838_ == 0)
{
v___x_825_ = v_x_821_;
v_isShared_826_ = v_isSharedCheck_838_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_tail_823_);
lean_inc(v_head_822_);
lean_dec(v_x_821_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_838_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
lean_inc(v_x_819_);
if (v_isShared_826_ == 0)
{
lean_ctor_set_tag(v___x_825_, 5);
lean_ctor_set(v___x_825_, 1, v_x_819_);
lean_ctor_set(v___x_825_, 0, v_x_820_);
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_x_820_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_x_819_);
v___x_828_ = v_reuseFailAlloc_837_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = ((lean_object*)(l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_831_ = l_String_quote(v_head_822_);
v___x_832_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
v___x_833_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_830_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = l_Repr_addAppParen(v___x_833_, v___x_829_);
v___x_835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_828_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v_x_820_ = v___x_835_;
v_x_821_ = v_tail_823_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_839_, lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
if (lean_obj_tag(v_x_841_) == 0)
{
lean_dec(v_x_839_);
return v_x_840_;
}
else
{
lean_object* v_head_842_; lean_object* v_tail_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_858_; 
v_head_842_ = lean_ctor_get(v_x_841_, 0);
v_tail_843_ = lean_ctor_get(v_x_841_, 1);
v_isSharedCheck_858_ = !lean_is_exclusive(v_x_841_);
if (v_isSharedCheck_858_ == 0)
{
v___x_845_ = v_x_841_;
v_isShared_846_ = v_isSharedCheck_858_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_tail_843_);
lean_inc(v_head_842_);
lean_dec(v_x_841_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_858_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
lean_inc(v_x_839_);
if (v_isShared_846_ == 0)
{
lean_ctor_set_tag(v___x_845_, 5);
lean_ctor_set(v___x_845_, 1, v_x_839_);
lean_ctor_set(v___x_845_, 0, v_x_840_);
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_x_840_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_x_839_);
v___x_848_ = v_reuseFailAlloc_857_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_849_ = lean_unsigned_to_nat(0u);
v___x_850_ = ((lean_object*)(l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_851_ = l_String_quote(v_head_842_);
v___x_852_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
v___x_853_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_850_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = l_Repr_addAppParen(v___x_853_, v___x_849_);
v___x_855_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_848_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2_spec__4(v_x_839_, v___x_855_, v_tail_843_);
return v___x_856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1(lean_object* v_x_859_, lean_object* v_x_860_){
_start:
{
if (lean_obj_tag(v_x_859_) == 0)
{
lean_object* v___x_861_; 
lean_dec(v_x_860_);
v___x_861_ = lean_box(0);
return v___x_861_;
}
else
{
lean_object* v_tail_862_; 
v_tail_862_ = lean_ctor_get(v_x_859_, 1);
if (lean_obj_tag(v_tail_862_) == 0)
{
lean_object* v_head_863_; lean_object* v___x_864_; 
lean_dec(v_x_860_);
v_head_863_ = lean_ctor_get(v_x_859_, 0);
lean_inc(v_head_863_);
lean_dec_ref_known(v_x_859_, 2);
v___x_864_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0(v_head_863_);
return v___x_864_;
}
else
{
lean_object* v_head_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
lean_inc(v_tail_862_);
v_head_865_ = lean_ctor_get(v_x_859_, 0);
lean_inc(v_head_865_);
lean_dec_ref_known(v_x_859_, 2);
v___x_866_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0(v_head_865_);
v___x_867_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2(v_x_860_, v___x_866_, v_tail_862_);
return v___x_867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0(lean_object* v_xs_868_){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_869_ = lean_array_get_size(v_xs_868_);
v___x_870_ = lean_unsigned_to_nat(0u);
v___x_871_ = lean_nat_dec_eq(v___x_869_, v___x_870_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_872_ = lean_array_to_list(v_xs_868_);
v___x_873_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_874_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1(v___x_872_, v___x_873_);
v___x_875_ = lean_obj_once(&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4);
v___x_876_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5));
v___x_877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
lean_ctor_set(v___x_877_, 1, v___x_874_);
v___x_878_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6));
v___x_879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_875_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = l_Std_Format_fill(v___x_880_);
return v___x_881_;
}
else
{
lean_object* v___x_882_; 
lean_dec_ref(v_xs_868_);
v___x_882_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8));
return v___x_882_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__1_spec__3(lean_object* v_x_883_, lean_object* v_x_884_, lean_object* v_x_885_){
_start:
{
if (lean_obj_tag(v_x_885_) == 0)
{
lean_dec(v_x_883_);
return v_x_884_;
}
else
{
lean_object* v_head_886_; lean_object* v_tail_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_897_; 
v_head_886_ = lean_ctor_get(v_x_885_, 0);
v_tail_887_ = lean_ctor_get(v_x_885_, 1);
v_isSharedCheck_897_ = !lean_is_exclusive(v_x_885_);
if (v_isSharedCheck_897_ == 0)
{
v___x_889_ = v_x_885_;
v_isShared_890_ = v_isSharedCheck_897_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_tail_887_);
lean_inc(v_head_886_);
lean_dec(v_x_885_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_897_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
lean_inc(v_x_883_);
if (v_isShared_890_ == 0)
{
lean_ctor_set_tag(v___x_889_, 5);
lean_ctor_set(v___x_889_, 1, v_x_883_);
lean_ctor_set(v___x_889_, 0, v_x_884_);
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_x_884_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_x_883_);
v___x_892_ = v_reuseFailAlloc_896_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = l_Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0(v_head_886_);
v___x_894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v_x_884_ = v___x_894_;
v_x_885_ = v_tail_887_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__1(lean_object* v_x_898_, lean_object* v_x_899_){
_start:
{
if (lean_obj_tag(v_x_898_) == 0)
{
lean_object* v___x_900_; 
lean_dec(v_x_899_);
v___x_900_ = lean_box(0);
return v___x_900_;
}
else
{
lean_object* v_tail_901_; 
v_tail_901_ = lean_ctor_get(v_x_898_, 1);
if (lean_obj_tag(v_tail_901_) == 0)
{
lean_object* v_head_902_; lean_object* v___x_903_; 
lean_dec(v_x_899_);
v_head_902_ = lean_ctor_get(v_x_898_, 0);
lean_inc(v_head_902_);
lean_dec_ref_known(v_x_898_, 2);
v___x_903_ = l_Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0(v_head_902_);
return v___x_903_;
}
else
{
lean_object* v_head_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
lean_inc(v_tail_901_);
v_head_904_ = lean_ctor_get(v_x_898_, 0);
lean_inc(v_head_904_);
lean_dec_ref_known(v_x_898_, 2);
v___x_905_ = l_Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0(v_head_904_);
v___x_906_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__1_spec__3(v_x_899_, v___x_905_, v_tail_901_);
return v___x_906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0(lean_object* v_xs_907_){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_908_ = lean_array_get_size(v_xs_907_);
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = lean_nat_dec_eq(v___x_908_, v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_911_ = lean_array_to_list(v_xs_907_);
v___x_912_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_913_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__1(v___x_911_, v___x_912_);
v___x_914_ = lean_obj_once(&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4);
v___x_915_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5));
v___x_916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set(v___x_916_, 1, v___x_913_);
v___x_917_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6));
v___x_918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_914_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = l_Std_Format_fill(v___x_919_);
return v___x_920_;
}
else
{
lean_object* v___x_921_; 
lean_dec_ref(v_xs_907_);
v___x_921_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8));
return v___x_921_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprImportArtifacts_repr___redArg(lean_object* v_x_931_){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_932_ = ((lean_object*)(l_Lean_instReprImportArtifacts_repr___redArg___closed__3));
v___x_933_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__7, &l_Lean_instReprModuleHeader_repr___redArg___closed__7_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__7);
v___x_934_ = l_Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0(v_x_931_);
v___x_935_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = 0;
v___x_937_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set_uint8(v___x_937_, sizeof(void*)*1, v___x_936_);
v___x_938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_932_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__20, &l_Lean_instReprImport_repr___redArg___closed__20_once, _init_l_Lean_instReprImport_repr___redArg___closed__20);
v___x_940_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__21));
v___x_941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v___x_938_);
v___x_942_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__22));
v___x_943_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_939_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set_uint8(v___x_945_, sizeof(void*)*1, v___x_936_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprImportArtifacts_repr(lean_object* v_x_946_, lean_object* v_prec_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_instReprImportArtifacts_repr___redArg(v_x_946_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprImportArtifacts_repr___boxed(lean_object* v_x_949_, lean_object* v_prec_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_instReprImportArtifacts_repr(v_x_949_, v_prec_950_);
lean_dec(v_prec_950_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonImportArtifacts___lam__0(lean_object* v___x_958_, lean_object* v_x_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_Array_toJson___redArg(v___x_958_, v_x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonImportArtifacts___lam__0(lean_object* v___x_967_, lean_object* v_x_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_Array_fromJson_x3f___redArg(v___x_967_, v_x_968_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
v_a_978_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_969_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_969_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_olean_x3f(lean_object* v_arts_992_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = lean_array_get_size(v_arts_992_);
v___x_995_ = lean_nat_dec_lt(v___x_993_, v___x_994_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; 
v___x_996_ = lean_box(0);
return v___x_996_;
}
else
{
lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_997_ = lean_array_fget_borrowed(v_arts_992_, v___x_993_);
v___x_998_ = lean_array_get_size(v___x_997_);
v___x_999_ = lean_nat_dec_lt(v___x_993_, v___x_998_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_box(0);
return v___x_1000_;
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_array_fget_borrowed(v___x_997_, v___x_993_);
lean_inc(v___x_1001_);
v___x_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
return v___x_1002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_olean_x3f___boxed(lean_object* v_arts_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_ImportArtifacts_olean_x3f(v_arts_1003_);
lean_dec_ref(v_arts_1003_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanServer_x3f(lean_object* v_arts_1005_){
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
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1010_ = lean_array_fget_borrowed(v_arts_1005_, v___x_1006_);
v___x_1011_ = lean_unsigned_to_nat(1u);
v___x_1012_ = lean_array_get_size(v___x_1010_);
v___x_1013_ = lean_nat_dec_lt(v___x_1011_, v___x_1012_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_box(0);
return v___x_1014_;
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_array_fget_borrowed(v___x_1010_, v___x_1011_);
lean_inc(v___x_1015_);
v___x_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
return v___x_1016_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanServer_x3f___boxed(lean_object* v_arts_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_ImportArtifacts_oleanServer_x3f(v_arts_1017_);
lean_dec_ref(v_arts_1017_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanPrivate_x3f(lean_object* v_arts_1019_){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v___x_1020_ = lean_unsigned_to_nat(0u);
v___x_1021_ = lean_array_get_size(v_arts_1019_);
v___x_1022_ = lean_nat_dec_lt(v___x_1020_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_box(0);
return v___x_1023_;
}
else
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_1024_ = lean_array_fget_borrowed(v_arts_1019_, v___x_1020_);
v___x_1025_ = lean_unsigned_to_nat(2u);
v___x_1026_ = lean_array_get_size(v___x_1024_);
v___x_1027_ = lean_nat_dec_lt(v___x_1025_, v___x_1026_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_box(0);
return v___x_1028_;
}
else
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_array_fget_borrowed(v___x_1024_, v___x_1025_);
lean_inc(v___x_1029_);
v___x_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
return v___x_1030_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanPrivate_x3f___boxed(lean_object* v_arts_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_ImportArtifacts_oleanPrivate_x3f(v_arts_1031_);
lean_dec_ref(v_arts_1031_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_irSig_x3f(lean_object* v_arts_1033_){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1034_ = lean_unsigned_to_nat(1u);
v___x_1035_ = lean_array_get_size(v_arts_1033_);
v___x_1036_ = lean_nat_dec_lt(v___x_1034_, v___x_1035_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_box(0);
return v___x_1037_;
}
else
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_1038_ = lean_array_fget_borrowed(v_arts_1033_, v___x_1034_);
v___x_1039_ = lean_unsigned_to_nat(0u);
v___x_1040_ = lean_array_get_size(v___x_1038_);
v___x_1041_ = lean_nat_dec_lt(v___x_1039_, v___x_1040_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_box(0);
return v___x_1042_;
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_array_fget_borrowed(v___x_1038_, v___x_1039_);
lean_inc(v___x_1043_);
v___x_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
return v___x_1044_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_irSig_x3f___boxed(lean_object* v_arts_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_ImportArtifacts_irSig_x3f(v_arts_1045_);
lean_dec_ref(v_arts_1045_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_ir_x3f(lean_object* v_arts_1047_){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v___x_1048_ = lean_unsigned_to_nat(1u);
v___x_1049_ = lean_array_get_size(v_arts_1047_);
v___x_1050_ = lean_nat_dec_lt(v___x_1048_, v___x_1049_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_box(0);
return v___x_1051_;
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1052_ = lean_array_fget_borrowed(v_arts_1047_, v___x_1048_);
v___x_1053_ = lean_array_get_size(v___x_1052_);
v___x_1054_ = lean_nat_dec_lt(v___x_1048_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_box(0);
return v___x_1055_;
}
else
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_array_fget_borrowed(v___x_1052_, v___x_1048_);
lean_inc(v___x_1056_);
v___x_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_ir_x3f___boxed(lean_object* v_arts_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_ImportArtifacts_ir_x3f(v_arts_1058_);
lean_dec_ref(v_arts_1058_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanParts(uint8_t v_inServer_1062_, lean_object* v_arts_1063_){
_start:
{
lean_object* v_fnames_1065_; lean_object* v_fnames_1069_; lean_object* v___x_1070_; 
v_fnames_1069_ = ((lean_object*)(l_Lean_ImportArtifacts_oleanParts___closed__0));
v___x_1070_ = l_Lean_ImportArtifacts_olean_x3f(v_arts_1063_);
if (lean_obj_tag(v___x_1070_) == 1)
{
lean_object* v_val_1071_; lean_object* v_fnames_1072_; lean_object* v___x_1073_; 
v_val_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_val_1071_);
lean_dec_ref_known(v___x_1070_, 1);
v_fnames_1072_ = lean_array_push(v_fnames_1069_, v_val_1071_);
v___x_1073_ = l_Lean_ImportArtifacts_oleanServer_x3f(v_arts_1063_);
if (lean_obj_tag(v___x_1073_) == 1)
{
lean_object* v_val_1074_; 
v_val_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_val_1074_);
lean_dec_ref_known(v___x_1073_, 1);
if (v_inServer_1062_ == 0)
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_ImportArtifacts_oleanPrivate_x3f(v_arts_1063_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_dec(v_val_1074_);
v_fnames_1065_ = v_fnames_1072_;
goto v___jp_1064_;
}
else
{
lean_dec_ref_known(v___x_1077_, 1);
goto v___jp_1075_;
}
}
else
{
goto v___jp_1075_;
}
v___jp_1075_:
{
lean_object* v_fnames_1076_; 
v_fnames_1076_ = lean_array_push(v_fnames_1072_, v_val_1074_);
v_fnames_1065_ = v_fnames_1076_;
goto v___jp_1064_;
}
}
else
{
lean_dec(v___x_1073_);
return v_fnames_1072_;
}
}
else
{
lean_dec(v___x_1070_);
return v_fnames_1069_;
}
v___jp_1064_:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Lean_ImportArtifacts_oleanPrivate_x3f(v_arts_1063_);
if (lean_obj_tag(v___x_1066_) == 1)
{
lean_object* v_val_1067_; lean_object* v_fnames_1068_; 
v_val_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_val_1067_);
lean_dec_ref_known(v___x_1066_, 1);
v_fnames_1068_ = lean_array_push(v_fnames_1065_, v_val_1067_);
return v_fnames_1068_;
}
else
{
lean_dec(v___x_1066_);
return v_fnames_1065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanParts___boxed(lean_object* v_inServer_1078_, lean_object* v_arts_1079_){
_start:
{
uint8_t v_inServer_boxed_1080_; lean_object* v_res_1081_; 
v_inServer_boxed_1080_ = lean_unbox(v_inServer_1078_);
v_res_1081_ = l_Lean_ImportArtifacts_oleanParts(v_inServer_boxed_1080_, v_arts_1079_);
lean_dec_ref(v_arts_1079_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_irParts(lean_object* v_arts_1082_){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1083_ = lean_unsigned_to_nat(1u);
v___x_1084_ = lean_array_get_size(v_arts_1082_);
v___x_1085_ = lean_nat_dec_lt(v___x_1083_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; 
v___x_1086_ = ((lean_object*)(l_Lean_ImportArtifacts_oleanParts___closed__0));
return v___x_1086_;
}
else
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_array_fget_borrowed(v_arts_1082_, v___x_1083_);
lean_inc(v___x_1087_);
return v___x_1087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_irParts___boxed(lean_object* v_arts_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_ImportArtifacts_irParts(v_arts_1088_);
lean_dec_ref(v_arts_1088_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(lean_object* v_x_1096_, lean_object* v_x_1097_){
_start:
{
if (lean_obj_tag(v_x_1096_) == 0)
{
lean_object* v___x_1098_; 
v___x_1098_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__1));
return v___x_1098_;
}
else
{
lean_object* v_val_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1114_; 
v_val_1099_ = lean_ctor_get(v_x_1096_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_x_1096_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1101_ = v_x_1096_;
v_isShared_1102_ = v_isSharedCheck_1114_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_val_1099_);
lean_dec(v_x_1096_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1114_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1103_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__3));
v___x_1104_ = lean_unsigned_to_nat(1024u);
v___x_1105_ = ((lean_object*)(l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_1106_ = l_String_quote(v_val_1099_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set_tag(v___x_1101_, 3);
lean_ctor_set(v___x_1101_, 0, v___x_1106_);
v___x_1108_ = v___x_1101_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1105_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = l_Repr_addAppParen(v___x_1109_, v___x_1104_);
v___x_1111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1103_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = l_Repr_addAppParen(v___x_1111_, v_x_1097_);
return v___x_1112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___boxed(lean_object* v_x_1115_, lean_object* v_x_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_x_1115_, v_x_1116_);
lean_dec(v_x_1116_);
return v_res_1117_;
}
}
static lean_object* _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = lean_unsigned_to_nat(9u);
v___x_1128_ = lean_nat_to_int(v___x_1127_);
return v___x_1128_;
}
}
static lean_object* _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_unsigned_to_nat(16u);
v___x_1136_ = lean_nat_to_int(v___x_1135_);
return v___x_1136_;
}
}
static lean_object* _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_unsigned_to_nat(17u);
v___x_1141_ = lean_nat_to_int(v___x_1140_);
return v___x_1141_;
}
}
static lean_object* _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_unsigned_to_nat(7u);
v___x_1152_ = lean_nat_to_int(v___x_1151_);
return v___x_1152_;
}
}
static lean_object* _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = lean_unsigned_to_nat(6u);
v___x_1157_ = lean_nat_to_int(v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleArtifacts_repr___redArg(lean_object* v_x_1161_){
_start:
{
lean_object* v_lean_x3f_1162_; lean_object* v_olean_x3f_1163_; lean_object* v_oleanServer_x3f_1164_; lean_object* v_oleanPrivate_x3f_1165_; lean_object* v_ilean_x3f_1166_; lean_object* v_irSig_x3f_1167_; lean_object* v_ir_x3f_1168_; lean_object* v_c_x3f_1169_; lean_object* v_bc_x3f_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v_lean_x3f_1162_ = lean_ctor_get(v_x_1161_, 0);
lean_inc(v_lean_x3f_1162_);
v_olean_x3f_1163_ = lean_ctor_get(v_x_1161_, 1);
lean_inc(v_olean_x3f_1163_);
v_oleanServer_x3f_1164_ = lean_ctor_get(v_x_1161_, 2);
lean_inc(v_oleanServer_x3f_1164_);
v_oleanPrivate_x3f_1165_ = lean_ctor_get(v_x_1161_, 3);
lean_inc(v_oleanPrivate_x3f_1165_);
v_ilean_x3f_1166_ = lean_ctor_get(v_x_1161_, 4);
lean_inc(v_ilean_x3f_1166_);
v_irSig_x3f_1167_ = lean_ctor_get(v_x_1161_, 5);
lean_inc(v_irSig_x3f_1167_);
v_ir_x3f_1168_ = lean_ctor_get(v_x_1161_, 6);
lean_inc(v_ir_x3f_1168_);
v_c_x3f_1169_ = lean_ctor_get(v_x_1161_, 7);
lean_inc(v_c_x3f_1169_);
v_bc_x3f_1170_ = lean_ctor_get(v_x_1161_, 8);
lean_inc(v_bc_x3f_1170_);
lean_dec_ref(v_x_1161_);
v___x_1171_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__5));
v___x_1172_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__3));
v___x_1173_ = lean_obj_once(&l_Lean_instReprModuleArtifacts_repr___redArg___closed__4, &l_Lean_instReprModuleArtifacts_repr___redArg___closed__4_once, _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__4);
v___x_1174_ = lean_unsigned_to_nat(0u);
v___x_1175_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_lean_x3f_1162_, v___x_1174_);
v___x_1176_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1173_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = 0;
v___x_1178_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1178_, 0, v___x_1176_);
lean_ctor_set_uint8(v___x_1178_, sizeof(void*)*1, v___x_1177_);
v___x_1179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1172_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__9));
v___x_1181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1179_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = lean_box(1);
v___x_1183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__6));
v___x_1185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
lean_ctor_set(v___x_1186_, 1, v___x_1171_);
v___x_1187_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__7, &l_Lean_instReprImport_repr___redArg___closed__7_once, _init_l_Lean_instReprImport_repr___redArg___closed__7);
v___x_1188_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_olean_x3f_1163_, v___x_1174_);
v___x_1189_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
lean_ctor_set_uint8(v___x_1190_, sizeof(void*)*1, v___x_1177_);
v___x_1191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1186_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
lean_ctor_set(v___x_1192_, 1, v___x_1180_);
v___x_1193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
lean_ctor_set(v___x_1193_, 1, v___x_1182_);
v___x_1194_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__8));
v___x_1195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1193_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
lean_ctor_set(v___x_1196_, 1, v___x_1171_);
v___x_1197_ = lean_obj_once(&l_Lean_instReprModuleArtifacts_repr___redArg___closed__9, &l_Lean_instReprModuleArtifacts_repr___redArg___closed__9_once, _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__9);
v___x_1198_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_oleanServer_x3f_1164_, v___x_1174_);
v___x_1199_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1197_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
lean_ctor_set_uint8(v___x_1200_, sizeof(void*)*1, v___x_1177_);
v___x_1201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1196_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
lean_ctor_set(v___x_1202_, 1, v___x_1180_);
v___x_1203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
lean_ctor_set(v___x_1203_, 1, v___x_1182_);
v___x_1204_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__11));
v___x_1205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set(v___x_1206_, 1, v___x_1171_);
v___x_1207_ = lean_obj_once(&l_Lean_instReprModuleArtifacts_repr___redArg___closed__12, &l_Lean_instReprModuleArtifacts_repr___redArg___closed__12_once, _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__12);
v___x_1208_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_oleanPrivate_x3f_1165_, v___x_1174_);
v___x_1209_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1207_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
lean_ctor_set_uint8(v___x_1210_, sizeof(void*)*1, v___x_1177_);
v___x_1211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1206_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
v___x_1212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
lean_ctor_set(v___x_1212_, 1, v___x_1180_);
v___x_1213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set(v___x_1213_, 1, v___x_1182_);
v___x_1214_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__14));
v___x_1215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1213_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
lean_ctor_set(v___x_1216_, 1, v___x_1171_);
v___x_1217_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_ilean_x3f_1166_, v___x_1174_);
v___x_1218_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1187_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
lean_ctor_set_uint8(v___x_1219_, sizeof(void*)*1, v___x_1177_);
v___x_1220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1216_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
v___x_1221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
lean_ctor_set(v___x_1221_, 1, v___x_1180_);
v___x_1222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v___x_1182_);
v___x_1223_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__16));
v___x_1224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1222_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set(v___x_1225_, 1, v___x_1171_);
v___x_1226_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_irSig_x3f_1167_, v___x_1174_);
v___x_1227_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1187_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
v___x_1228_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
lean_ctor_set_uint8(v___x_1228_, sizeof(void*)*1, v___x_1177_);
v___x_1229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1225_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
v___x_1230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
lean_ctor_set(v___x_1230_, 1, v___x_1180_);
v___x_1231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
lean_ctor_set(v___x_1231_, 1, v___x_1182_);
v___x_1232_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__18));
v___x_1233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1231_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
lean_ctor_set(v___x_1234_, 1, v___x_1171_);
v___x_1235_ = lean_obj_once(&l_Lean_instReprModuleArtifacts_repr___redArg___closed__19, &l_Lean_instReprModuleArtifacts_repr___redArg___closed__19_once, _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__19);
v___x_1236_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_ir_x3f_1168_, v___x_1174_);
v___x_1237_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1235_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
lean_ctor_set_uint8(v___x_1238_, sizeof(void*)*1, v___x_1177_);
v___x_1239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1234_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
lean_ctor_set(v___x_1240_, 1, v___x_1180_);
v___x_1241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
lean_ctor_set(v___x_1241_, 1, v___x_1182_);
v___x_1242_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__21));
v___x_1243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1241_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
v___x_1244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
lean_ctor_set(v___x_1244_, 1, v___x_1171_);
v___x_1245_ = lean_obj_once(&l_Lean_instReprModuleArtifacts_repr___redArg___closed__22, &l_Lean_instReprModuleArtifacts_repr___redArg___closed__22_once, _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__22);
v___x_1246_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_c_x3f_1169_, v___x_1174_);
v___x_1247_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1245_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
v___x_1248_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
lean_ctor_set_uint8(v___x_1248_, sizeof(void*)*1, v___x_1177_);
v___x_1249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1244_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
lean_ctor_set(v___x_1250_, 1, v___x_1180_);
v___x_1251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
lean_ctor_set(v___x_1251_, 1, v___x_1182_);
v___x_1252_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__24));
v___x_1253_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1251_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
v___x_1254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
lean_ctor_set(v___x_1254_, 1, v___x_1171_);
v___x_1255_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_bc_x3f_1170_, v___x_1174_);
v___x_1256_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1235_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
lean_ctor_set_uint8(v___x_1257_, sizeof(void*)*1, v___x_1177_);
v___x_1258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1254_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__20, &l_Lean_instReprImport_repr___redArg___closed__20_once, _init_l_Lean_instReprImport_repr___redArg___closed__20);
v___x_1260_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__21));
v___x_1261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
lean_ctor_set(v___x_1261_, 1, v___x_1258_);
v___x_1262_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__22));
v___x_1263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1261_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
v___x_1264_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1259_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
lean_ctor_set_uint8(v___x_1265_, sizeof(void*)*1, v___x_1177_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleArtifacts_repr(lean_object* v_x_1266_, lean_object* v_prec_1267_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_instReprModuleArtifacts_repr___redArg(v_x_1266_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleArtifacts_repr___boxed(lean_object* v_x_1269_, lean_object* v_prec_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_instReprModuleArtifacts_repr(v_x_1269_, v_prec_1270_);
lean_dec(v_prec_1270_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(lean_object* v_k_1278_, lean_object* v_x_1279_){
_start:
{
if (lean_obj_tag(v_x_1279_) == 0)
{
lean_object* v___x_1280_; 
lean_dec_ref(v_k_1278_);
v___x_1280_ = lean_box(0);
return v___x_1280_;
}
else
{
lean_object* v_val_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1291_; 
v_val_1281_ = lean_ctor_get(v_x_1279_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_x_1279_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1283_ = v_x_1279_;
v_isShared_1284_ = v_isSharedCheck_1291_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_val_1281_);
lean_dec(v_x_1279_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1291_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
lean_ctor_set_tag(v___x_1283_, 3);
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_val_1281_);
v___x_1286_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1287_, 0, v_k_1278_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = lean_box(0);
v___x_1289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1287_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
return v___x_1289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonModuleArtifacts_toJson(lean_object* v_x_1301_){
_start:
{
lean_object* v_lean_x3f_1302_; lean_object* v_olean_x3f_1303_; lean_object* v_oleanServer_x3f_1304_; lean_object* v_oleanPrivate_x3f_1305_; lean_object* v_ilean_x3f_1306_; lean_object* v_irSig_x3f_1307_; lean_object* v_ir_x3f_1308_; lean_object* v_c_x3f_1309_; lean_object* v_bc_x3f_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v_lean_x3f_1302_ = lean_ctor_get(v_x_1301_, 0);
lean_inc(v_lean_x3f_1302_);
v_olean_x3f_1303_ = lean_ctor_get(v_x_1301_, 1);
lean_inc(v_olean_x3f_1303_);
v_oleanServer_x3f_1304_ = lean_ctor_get(v_x_1301_, 2);
lean_inc(v_oleanServer_x3f_1304_);
v_oleanPrivate_x3f_1305_ = lean_ctor_get(v_x_1301_, 3);
lean_inc(v_oleanPrivate_x3f_1305_);
v_ilean_x3f_1306_ = lean_ctor_get(v_x_1301_, 4);
lean_inc(v_ilean_x3f_1306_);
v_irSig_x3f_1307_ = lean_ctor_get(v_x_1301_, 5);
lean_inc(v_irSig_x3f_1307_);
v_ir_x3f_1308_ = lean_ctor_get(v_x_1301_, 6);
lean_inc(v_ir_x3f_1308_);
v_c_x3f_1309_ = lean_ctor_get(v_x_1301_, 7);
lean_inc(v_c_x3f_1309_);
v_bc_x3f_1310_ = lean_ctor_get(v_x_1301_, 8);
lean_inc(v_bc_x3f_1310_);
lean_dec_ref(v_x_1301_);
v___x_1311_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__0));
v___x_1312_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1311_, v_lean_x3f_1302_);
v___x_1313_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__1));
v___x_1314_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1313_, v_olean_x3f_1303_);
v___x_1315_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__2));
v___x_1316_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1315_, v_oleanServer_x3f_1304_);
v___x_1317_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__3));
v___x_1318_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1317_, v_oleanPrivate_x3f_1305_);
v___x_1319_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__4));
v___x_1320_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1319_, v_ilean_x3f_1306_);
v___x_1321_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__5));
v___x_1322_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1321_, v_irSig_x3f_1307_);
v___x_1323_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__6));
v___x_1324_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1323_, v_ir_x3f_1308_);
v___x_1325_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__7));
v___x_1326_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1325_, v_c_x3f_1309_);
v___x_1327_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__8));
v___x_1328_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1327_, v_bc_x3f_1310_);
v___x_1329_ = lean_box(0);
v___x_1330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1328_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v___x_1331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1326_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1324_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
v___x_1333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1322_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
v___x_1334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1320_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
v___x_1335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1318_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
v___x_1336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1316_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
v___x_1337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1314_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
v___x_1338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1312_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
v___x_1339_ = ((lean_object*)(l_Lean_instToJsonImport_toJson___closed__0));
v___x_1340_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(v___x_1338_, v___x_1339_);
v___x_1341_ = l_Lean_Json_mkObj(v___x_1340_);
lean_dec(v___x_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0(lean_object* v_x_1346_){
_start:
{
if (lean_obj_tag(v_x_1346_) == 0)
{
lean_object* v___x_1347_; 
v___x_1347_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0___closed__0));
return v___x_1347_;
}
else
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Lean_Json_getStr_x3f(v_x_1346_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1348_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1348_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1365_; 
v_a_1357_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1359_ = v___x_1348_;
v_isShared_1360_ = v_isSharedCheck_1365_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1348_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1365_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; lean_object* v___x_1363_; 
v___x_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1361_, 0, v_a_1357_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v___x_1361_);
v___x_1363_ = v___x_1359_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(lean_object* v_j_1366_, lean_object* v_k_1367_){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = l_Lean_Json_getObjValD(v_j_1366_, v_k_1367_);
v___x_1369_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0(v___x_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0___boxed(lean_object* v_j_1370_, lean_object* v_k_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_j_1370_, v_k_1371_);
lean_dec_ref(v_k_1371_);
return v_res_1372_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1377_ = 1;
v___x_1378_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__1));
v___x_1379_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1378_, v___x_1377_);
return v___x_1379_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__4));
v___x_1381_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2);
v___x_1382_ = lean_string_append(v___x_1381_, v___x_1380_);
return v___x_1382_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1385_ = 1;
v___x_1386_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__4));
v___x_1387_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1386_, v___x_1385_);
return v___x_1387_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1388_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5);
v___x_1389_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1390_ = lean_string_append(v___x_1389_, v___x_1388_);
return v___x_1390_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1391_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1392_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6);
v___x_1393_ = lean_string_append(v___x_1392_, v___x_1391_);
return v___x_1393_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1396_ = 1;
v___x_1397_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__8));
v___x_1398_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1397_, v___x_1396_);
return v___x_1398_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1399_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9);
v___x_1400_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1401_ = lean_string_append(v___x_1400_, v___x_1399_);
return v___x_1401_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1402_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1403_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10);
v___x_1404_ = lean_string_append(v___x_1403_, v___x_1402_);
return v___x_1404_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13(void){
_start:
{
uint8_t v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1407_ = 1;
v___x_1408_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__12));
v___x_1409_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1408_, v___x_1407_);
return v___x_1409_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1410_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13);
v___x_1411_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1412_ = lean_string_append(v___x_1411_, v___x_1410_);
return v___x_1412_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1413_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1414_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14);
v___x_1415_ = lean_string_append(v___x_1414_, v___x_1413_);
return v___x_1415_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17(void){
_start:
{
uint8_t v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1418_ = 1;
v___x_1419_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__16));
v___x_1420_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1419_, v___x_1418_);
return v___x_1420_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18(void){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1421_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17);
v___x_1422_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1423_ = lean_string_append(v___x_1422_, v___x_1421_);
return v___x_1423_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19(void){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1424_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1425_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18);
v___x_1426_ = lean_string_append(v___x_1425_, v___x_1424_);
return v___x_1426_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1429_ = 1;
v___x_1430_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__20));
v___x_1431_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1430_, v___x_1429_);
return v___x_1431_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1432_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21);
v___x_1433_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1434_ = lean_string_append(v___x_1433_, v___x_1432_);
return v___x_1434_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1435_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1436_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22);
v___x_1437_ = lean_string_append(v___x_1436_, v___x_1435_);
return v___x_1437_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25(void){
_start:
{
uint8_t v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1440_ = 1;
v___x_1441_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__24));
v___x_1442_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1441_, v___x_1440_);
return v___x_1442_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26(void){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1443_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25);
v___x_1444_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1445_ = lean_string_append(v___x_1444_, v___x_1443_);
return v___x_1445_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27(void){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1446_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1447_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26);
v___x_1448_ = lean_string_append(v___x_1447_, v___x_1446_);
return v___x_1448_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29(void){
_start:
{
uint8_t v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1451_ = 1;
v___x_1452_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__28));
v___x_1453_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1452_, v___x_1451_);
return v___x_1453_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30(void){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1454_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29);
v___x_1455_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1456_ = lean_string_append(v___x_1455_, v___x_1454_);
return v___x_1456_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1457_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1458_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30);
v___x_1459_ = lean_string_append(v___x_1458_, v___x_1457_);
return v___x_1459_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33(void){
_start:
{
uint8_t v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1462_ = 1;
v___x_1463_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__32));
v___x_1464_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1463_, v___x_1462_);
return v___x_1464_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34(void){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1465_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33);
v___x_1466_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1467_ = lean_string_append(v___x_1466_, v___x_1465_);
return v___x_1467_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1468_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1469_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34);
v___x_1470_ = lean_string_append(v___x_1469_, v___x_1468_);
return v___x_1470_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__37(void){
_start:
{
uint8_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1473_ = 1;
v___x_1474_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__36));
v___x_1475_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1474_, v___x_1473_);
return v___x_1475_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__38(void){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1476_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__37, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__37_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__37);
v___x_1477_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1478_ = lean_string_append(v___x_1477_, v___x_1476_);
return v___x_1478_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__39(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1479_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1480_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__38, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__38_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__38);
v___x_1481_ = lean_string_append(v___x_1480_, v___x_1479_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson(lean_object* v_json_1482_){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__0));
lean_inc(v_json_1482_);
v___x_1484_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1482_, v___x_1483_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1494_; 
lean_dec(v_json_1482_);
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1494_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1494_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1489_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7);
v___x_1490_ = lean_string_append(v___x_1489_, v_a_1485_);
lean_dec(v_a_1485_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 0, v___x_1490_);
v___x_1492_ = v___x_1487_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
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
lean_object* v_a_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v_a_1495_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1495_);
lean_dec_ref_known(v___x_1484_, 1);
v___x_1496_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__1));
lean_inc(v_json_1482_);
v___x_1497_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1482_, v___x_1496_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v_a_1495_);
lean_dec(v_json_1482_);
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
v___x_1502_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11);
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
v___x_1509_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__2));
lean_inc(v_json_1482_);
v___x_1510_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1482_, v___x_1509_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1520_; 
lean_dec(v_a_1508_);
lean_dec(v_a_1495_);
lean_dec(v_json_1482_);
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
v___x_1515_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15);
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
v___x_1522_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__3));
lean_inc(v_json_1482_);
v___x_1523_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1482_, v___x_1522_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1533_; 
lean_dec(v_a_1521_);
lean_dec(v_a_1508_);
lean_dec(v_a_1495_);
lean_dec(v_json_1482_);
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
v___x_1528_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19);
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
v___x_1535_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__4));
lean_inc(v_json_1482_);
v___x_1536_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1482_, v___x_1535_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1546_; 
lean_dec(v_a_1534_);
lean_dec(v_a_1521_);
lean_dec(v_a_1508_);
lean_dec(v_a_1495_);
lean_dec(v_json_1482_);
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
v___x_1541_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23);
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
v___x_1548_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__5));
lean_inc(v_json_1482_);
v___x_1549_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1482_, v___x_1548_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1559_; 
lean_dec(v_a_1547_);
lean_dec(v_a_1534_);
lean_dec(v_a_1521_);
lean_dec(v_a_1508_);
lean_dec(v_a_1495_);
lean_dec(v_json_1482_);
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
v___x_1554_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27);
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
v___x_1561_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__6));
lean_inc(v_json_1482_);
v___x_1562_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1482_, v___x_1561_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1572_; 
lean_dec(v_a_1560_);
lean_dec(v_a_1547_);
lean_dec(v_a_1534_);
lean_dec(v_a_1521_);
lean_dec(v_a_1508_);
lean_dec(v_a_1495_);
lean_dec(v_json_1482_);
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
v___x_1567_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31);
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
v___x_1574_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__7));
lean_inc(v_json_1482_);
v___x_1575_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1482_, v___x_1574_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1585_; 
lean_dec(v_a_1573_);
lean_dec(v_a_1560_);
lean_dec(v_a_1547_);
lean_dec(v_a_1534_);
lean_dec(v_a_1521_);
lean_dec(v_a_1508_);
lean_dec(v_a_1495_);
lean_dec(v_json_1482_);
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
v___x_1580_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35);
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
v___x_1587_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__8));
v___x_1588_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1482_, v___x_1587_);
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
lean_dec(v_a_1495_);
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
v___x_1593_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__39, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__39_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__39);
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
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1607_; 
v_a_1599_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1601_ = v___x_1588_;
v_isShared_1602_ = v_isSharedCheck_1607_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1588_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1607_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1603_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1603_, 0, v_a_1495_);
lean_ctor_set(v___x_1603_, 1, v_a_1508_);
lean_ctor_set(v___x_1603_, 2, v_a_1521_);
lean_ctor_set(v___x_1603_, 3, v_a_1534_);
lean_ctor_set(v___x_1603_, 4, v_a_1547_);
lean_ctor_set(v___x_1603_, 5, v_a_1560_);
lean_ctor_set(v___x_1603_, 6, v_a_1573_);
lean_ctor_set(v___x_1603_, 7, v_a_1586_);
lean_ctor_set(v___x_1603_, 8, v_a_1599_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v___x_1603_);
v___x_1605_ = v___x_1601_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
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
LEAN_EXPORT lean_object* l_Lean_ModuleArtifacts_oleanParts(lean_object* v_arts_1610_){
_start:
{
lean_object* v_olean_x3f_1611_; lean_object* v_oleanServer_x3f_1612_; lean_object* v_oleanPrivate_x3f_1613_; lean_object* v_fnames_1614_; 
v_olean_x3f_1611_ = lean_ctor_get(v_arts_1610_, 1);
lean_inc(v_olean_x3f_1611_);
v_oleanServer_x3f_1612_ = lean_ctor_get(v_arts_1610_, 2);
lean_inc(v_oleanServer_x3f_1612_);
v_oleanPrivate_x3f_1613_ = lean_ctor_get(v_arts_1610_, 3);
lean_inc(v_oleanPrivate_x3f_1613_);
lean_dec_ref(v_arts_1610_);
v_fnames_1614_ = ((lean_object*)(l_Lean_ImportArtifacts_oleanParts___closed__0));
if (lean_obj_tag(v_olean_x3f_1611_) == 1)
{
lean_object* v_val_1615_; lean_object* v_fnames_1616_; 
v_val_1615_ = lean_ctor_get(v_olean_x3f_1611_, 0);
lean_inc(v_val_1615_);
lean_dec_ref_known(v_olean_x3f_1611_, 1);
v_fnames_1616_ = lean_array_push(v_fnames_1614_, v_val_1615_);
if (lean_obj_tag(v_oleanServer_x3f_1612_) == 1)
{
lean_object* v_val_1617_; lean_object* v_fnames_1618_; 
v_val_1617_ = lean_ctor_get(v_oleanServer_x3f_1612_, 0);
lean_inc(v_val_1617_);
lean_dec_ref_known(v_oleanServer_x3f_1612_, 1);
v_fnames_1618_ = lean_array_push(v_fnames_1616_, v_val_1617_);
if (lean_obj_tag(v_oleanPrivate_x3f_1613_) == 1)
{
lean_object* v_val_1619_; lean_object* v_fnames_1620_; 
v_val_1619_ = lean_ctor_get(v_oleanPrivate_x3f_1613_, 0);
lean_inc(v_val_1619_);
lean_dec_ref_known(v_oleanPrivate_x3f_1613_, 1);
v_fnames_1620_ = lean_array_push(v_fnames_1618_, v_val_1619_);
return v_fnames_1620_;
}
else
{
lean_dec(v_oleanPrivate_x3f_1613_);
return v_fnames_1618_;
}
}
else
{
lean_dec(v_oleanPrivate_x3f_1613_);
lean_dec(v_oleanServer_x3f_1612_);
return v_fnames_1616_;
}
}
else
{
lean_dec(v_oleanPrivate_x3f_1613_);
lean_dec(v_oleanServer_x3f_1612_);
lean_dec(v_olean_x3f_1611_);
return v_fnames_1614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleArtifacts_irParts(lean_object* v_arts_1621_){
_start:
{
lean_object* v_irSig_x3f_1622_; lean_object* v_ir_x3f_1623_; lean_object* v_fnames_1624_; 
v_irSig_x3f_1622_ = lean_ctor_get(v_arts_1621_, 5);
lean_inc(v_irSig_x3f_1622_);
v_ir_x3f_1623_ = lean_ctor_get(v_arts_1621_, 6);
lean_inc(v_ir_x3f_1623_);
lean_dec_ref(v_arts_1621_);
v_fnames_1624_ = ((lean_object*)(l_Lean_ImportArtifacts_oleanParts___closed__0));
if (lean_obj_tag(v_irSig_x3f_1622_) == 1)
{
lean_object* v_val_1625_; lean_object* v_fnames_1626_; 
v_val_1625_ = lean_ctor_get(v_irSig_x3f_1622_, 0);
lean_inc(v_val_1625_);
lean_dec_ref_known(v_irSig_x3f_1622_, 1);
v_fnames_1626_ = lean_array_push(v_fnames_1624_, v_val_1625_);
if (lean_obj_tag(v_ir_x3f_1623_) == 1)
{
lean_object* v_val_1627_; lean_object* v_fnames_1628_; 
v_val_1627_ = lean_ctor_get(v_ir_x3f_1623_, 0);
lean_inc(v_val_1627_);
lean_dec_ref_known(v_ir_x3f_1623_, 1);
v_fnames_1628_ = lean_array_push(v_fnames_1626_, v_val_1627_);
return v_fnames_1628_;
}
else
{
lean_dec(v_ir_x3f_1623_);
return v_fnames_1626_;
}
}
else
{
lean_dec(v_ir_x3f_1623_);
lean_dec(v_irSig_x3f_1622_);
return v_fnames_1624_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0(lean_object* v_x_1629_, lean_object* v_x_1630_){
_start:
{
if (lean_obj_tag(v_x_1629_) == 0)
{
lean_object* v___x_1631_; 
v___x_1631_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__1));
return v___x_1631_;
}
else
{
lean_object* v_val_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1643_; 
v_val_1632_ = lean_ctor_get(v_x_1629_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v_x_1629_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1634_ = v_x_1629_;
v_isShared_1635_ = v_isSharedCheck_1643_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_val_1632_);
lean_dec(v_x_1629_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1643_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1639_; 
v___x_1636_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__3));
v___x_1637_ = l_String_quote(v_val_1632_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set_tag(v___x_1634_, 3);
lean_ctor_set(v___x_1634_, 0, v___x_1637_);
v___x_1639_ = v___x_1634_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1637_);
v___x_1639_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1636_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = l_Repr_addAppParen(v___x_1640_, v_x_1630_);
return v___x_1641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0___boxed(lean_object* v_x_1644_, lean_object* v_x_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0(v_x_1644_, v_x_1645_);
lean_dec(v_x_1645_);
return v_res_1646_;
}
}
static lean_object* _init_l_Lean_instReprPlugin_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = lean_unsigned_to_nat(8u);
v___x_1657_ = lean_nat_to_int(v___x_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprPlugin_repr___redArg(lean_object* v_x_1661_){
_start:
{
lean_object* v_path_1662_; lean_object* v_initFn_x3f_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1701_; 
v_path_1662_ = lean_ctor_get(v_x_1661_, 0);
v_initFn_x3f_1663_ = lean_ctor_get(v_x_1661_, 1);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_x_1661_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1665_ = v_x_1661_;
v_isShared_1666_ = v_isSharedCheck_1701_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_initFn_x3f_1663_);
lean_inc(v_path_1662_);
lean_dec(v_x_1661_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1701_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1667_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__5));
v___x_1668_ = ((lean_object*)(l_Lean_instReprPlugin_repr___redArg___closed__3));
v___x_1669_ = lean_obj_once(&l_Lean_instReprPlugin_repr___redArg___closed__4, &l_Lean_instReprPlugin_repr___redArg___closed__4_once, _init_l_Lean_instReprPlugin_repr___redArg___closed__4);
v___x_1670_ = lean_unsigned_to_nat(0u);
v___x_1671_ = ((lean_object*)(l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_1672_ = l_String_quote(v_path_1662_);
v___x_1673_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set_tag(v___x_1665_, 5);
lean_ctor_set(v___x_1665_, 1, v___x_1673_);
lean_ctor_set(v___x_1665_, 0, v___x_1671_);
v___x_1675_ = v___x_1665_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1676_ = l_Repr_addAppParen(v___x_1675_, v___x_1670_);
v___x_1677_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1669_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
v___x_1678_ = 0;
v___x_1679_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set_uint8(v___x_1679_, sizeof(void*)*1, v___x_1678_);
v___x_1680_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1668_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
v___x_1681_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__9));
v___x_1682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1680_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
v___x_1683_ = lean_box(1);
v___x_1684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1682_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
v___x_1685_ = ((lean_object*)(l_Lean_instReprPlugin_repr___redArg___closed__6));
v___x_1686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1684_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
v___x_1687_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
lean_ctor_set(v___x_1687_, 1, v___x_1667_);
v___x_1688_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__4, &l_Lean_instReprModuleHeader_repr___redArg___closed__4_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__4);
v___x_1689_ = l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0(v_initFn_x3f_1663_, v___x_1670_);
v___x_1690_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1688_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
v___x_1691_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
lean_ctor_set_uint8(v___x_1691_, sizeof(void*)*1, v___x_1678_);
v___x_1692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1687_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
v___x_1693_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__20, &l_Lean_instReprImport_repr___redArg___closed__20_once, _init_l_Lean_instReprImport_repr___redArg___closed__20);
v___x_1694_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__21));
v___x_1695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
lean_ctor_set(v___x_1695_, 1, v___x_1692_);
v___x_1696_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__22));
v___x_1697_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1695_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
v___x_1698_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1693_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
lean_ctor_set_uint8(v___x_1699_, sizeof(void*)*1, v___x_1678_);
return v___x_1699_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprPlugin_repr(lean_object* v_x_1702_, lean_object* v_prec_1703_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Lean_instReprPlugin_repr___redArg(v_x_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprPlugin_repr___boxed(lean_object* v_x_1705_, lean_object* v_prec_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_instReprPlugin_repr(v_x_1705_, v_prec_1706_);
lean_dec(v_prec_1706_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonPlugin_toJson_spec__0(lean_object* v_k_1710_, lean_object* v_x_1711_){
_start:
{
if (lean_obj_tag(v_x_1711_) == 0)
{
lean_object* v___x_1712_; 
lean_dec_ref(v_k_1710_);
v___x_1712_ = lean_box(0);
return v___x_1712_;
}
else
{
lean_object* v_val_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1723_; 
v_val_1713_ = lean_ctor_get(v_x_1711_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v_x_1711_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1715_ = v_x_1711_;
v_isShared_1716_ = v_isSharedCheck_1723_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_val_1713_);
lean_dec(v_x_1711_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1723_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
lean_ctor_set_tag(v___x_1715_, 3);
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_val_1713_);
v___x_1718_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1719_, 0, v_k_1710_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
v___x_1720_ = lean_box(0);
v___x_1721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1719_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
return v___x_1721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonPlugin_toJson(lean_object* v_x_1725_){
_start:
{
lean_object* v_path_1726_; lean_object* v_initFn_x3f_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1745_; 
v_path_1726_ = lean_ctor_get(v_x_1725_, 0);
v_initFn_x3f_1727_ = lean_ctor_get(v_x_1725_, 1);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_x_1725_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1729_ = v_x_1725_;
v_isShared_1730_ = v_isSharedCheck_1745_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_initFn_x3f_1727_);
lean_inc(v_path_1726_);
lean_dec(v_x_1725_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1745_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1734_; 
v___x_1731_ = ((lean_object*)(l_Lean_instReprPlugin_repr___redArg___closed__0));
v___x_1732_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_path_1726_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 1, v___x_1732_);
lean_ctor_set(v___x_1729_, 0, v___x_1731_);
v___x_1734_ = v___x_1729_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1735_ = lean_box(0);
v___x_1736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1734_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
v___x_1737_ = ((lean_object*)(l_Lean_instToJsonPlugin_toJson___closed__0));
v___x_1738_ = l_Lean_Json_opt___at___00Lean_instToJsonPlugin_toJson_spec__0(v___x_1737_, v_initFn_x3f_1727_);
v___x_1739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
lean_ctor_set(v___x_1739_, 1, v___x_1735_);
v___x_1740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1736_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
v___x_1741_ = ((lean_object*)(l_Lean_instToJsonImport_toJson___closed__0));
v___x_1742_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(v___x_1740_, v___x_1741_);
v___x_1743_ = l_Lean_Json_mkObj(v___x_1742_);
lean_dec(v___x_1742_);
return v___x_1743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Plugin_ofFilePath(lean_object* v_path_1748_){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = lean_box(0);
v___x_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1750_, 0, v_path_1748_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__0(lean_object* v_j_1753_, lean_object* v_k_1754_){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = l_Lean_Json_getObjValD(v_j_1753_, v_k_1754_);
v___x_1756_ = l_Lean_Json_getStr_x3f(v___x_1755_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
v_a_1765_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1756_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1756_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__0___boxed(lean_object* v_j_1773_, lean_object* v_k_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__0(v_j_1773_, v_k_1774_);
lean_dec_ref(v_k_1774_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1_spec__1(lean_object* v_x_1776_){
_start:
{
if (lean_obj_tag(v_x_1776_) == 0)
{
lean_object* v___x_1777_; 
v___x_1777_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0___closed__0));
return v___x_1777_;
}
else
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_Json_getStr_x3f(v_x_1776_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1778_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1778_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1795_; 
v_a_1787_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1789_ = v___x_1778_;
v_isShared_1790_ = v_isSharedCheck_1795_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1778_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1795_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1791_, 0, v_a_1787_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1791_);
v___x_1793_ = v___x_1789_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1(lean_object* v_j_1796_, lean_object* v_k_1797_){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = l_Lean_Json_getObjValD(v_j_1796_, v_k_1797_);
v___x_1799_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1_spec__1(v___x_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1___boxed(lean_object* v_j_1800_, lean_object* v_k_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1(v_j_1800_, v_k_1801_);
lean_dec_ref(v_k_1801_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Plugin_fromJson_x3f(lean_object* v_data_1806_){
_start:
{
switch(lean_obj_tag(v_data_1806_))
{
case 3:
{
lean_object* v_s_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1815_; 
v_s_1807_ = lean_ctor_get(v_data_1806_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_data_1806_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1809_ = v_data_1806_;
v_isShared_1810_ = v_isSharedCheck_1815_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_s_1807_);
lean_dec(v_data_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1815_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1811_ = l_Lean_Plugin_ofFilePath(v_s_1807_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set_tag(v___x_1809_, 1);
lean_ctor_set(v___x_1809_, 0, v___x_1811_);
v___x_1813_ = v___x_1809_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
case 5:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = ((lean_object*)(l_Lean_instReprPlugin_repr___redArg___closed__0));
lean_inc_ref(v_data_1806_);
v___x_1817_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__0(v_data_1806_, v___x_1816_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_dec_ref_known(v_data_1806_, 1);
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v_a_1826_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_a_1826_);
lean_dec_ref_known(v___x_1817_, 1);
v___x_1827_ = ((lean_object*)(l_Lean_instToJsonPlugin_toJson___closed__0));
v___x_1828_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1(v_data_1806_, v___x_1827_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
lean_dec(v_a_1826_);
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1828_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1845_; 
v_a_1837_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1839_ = v___x_1828_;
v_isShared_1840_ = v_isSharedCheck_1845_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1828_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1845_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v_a_1826_);
lean_ctor_set(v___x_1841_, 1, v_a_1837_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1841_);
v___x_1843_ = v___x_1839_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
}
default: 
{
lean_object* v___x_1846_; 
lean_dec(v_data_1806_);
v___x_1846_ = ((lean_object*)(l_Lean_Plugin_fromJson_x3f___closed__1));
return v___x_1846_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2_spec__3_spec__5(lean_object* v_x_1849_, lean_object* v_x_1850_, lean_object* v_x_1851_){
_start:
{
if (lean_obj_tag(v_x_1851_) == 0)
{
lean_dec(v_x_1849_);
return v_x_1850_;
}
else
{
lean_object* v_head_1852_; lean_object* v_tail_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1862_; 
v_head_1852_ = lean_ctor_get(v_x_1851_, 0);
v_tail_1853_ = lean_ctor_get(v_x_1851_, 1);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_x_1851_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1855_ = v_x_1851_;
v_isShared_1856_ = v_isSharedCheck_1862_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_tail_1853_);
lean_inc(v_head_1852_);
lean_dec(v_x_1851_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1862_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
lean_inc(v_x_1849_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set_tag(v___x_1855_, 5);
lean_ctor_set(v___x_1855_, 1, v_x_1849_);
lean_ctor_set(v___x_1855_, 0, v_x_1850_);
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_x_1850_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_x_1849_);
v___x_1858_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1859_; 
v___x_1859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
lean_ctor_set(v___x_1859_, 1, v_head_1852_);
v_x_1850_ = v___x_1859_;
v_x_1851_ = v_tail_1853_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2_spec__3(lean_object* v_x_1863_, lean_object* v_x_1864_){
_start:
{
if (lean_obj_tag(v_x_1863_) == 0)
{
lean_object* v___x_1865_; 
lean_dec(v_x_1864_);
v___x_1865_ = lean_box(0);
return v___x_1865_;
}
else
{
lean_object* v_tail_1866_; 
v_tail_1866_ = lean_ctor_get(v_x_1863_, 1);
if (lean_obj_tag(v_tail_1866_) == 0)
{
lean_object* v_head_1867_; 
lean_dec(v_x_1864_);
v_head_1867_ = lean_ctor_get(v_x_1863_, 0);
lean_inc(v_head_1867_);
lean_dec_ref_known(v_x_1863_, 2);
return v_head_1867_;
}
else
{
lean_object* v_head_1868_; lean_object* v___x_1869_; 
lean_inc(v_tail_1866_);
v_head_1868_ = lean_ctor_get(v_x_1863_, 0);
lean_inc(v_head_1868_);
lean_dec_ref_known(v_x_1863_, 2);
v___x_1869_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2_spec__3_spec__5(v_x_1864_, v_head_1868_, v_tail_1866_);
return v___x_1869_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__0));
v___x_1873_ = lean_string_length(v___x_1872_);
return v___x_1873_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2, &l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2);
v___x_1875_ = lean_nat_to_int(v___x_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(lean_object* v_x_1880_){
_start:
{
lean_object* v_fst_1881_; lean_object* v_snd_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1905_; 
v_fst_1881_ = lean_ctor_get(v_x_1880_, 0);
v_snd_1882_ = lean_ctor_get(v_x_1880_, 1);
v_isSharedCheck_1905_ = !lean_is_exclusive(v_x_1880_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1884_ = v_x_1880_;
v_isShared_1885_ = v_isSharedCheck_1905_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_snd_1882_);
lean_inc(v_fst_1881_);
lean_dec(v_x_1880_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1905_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1886_ = lean_unsigned_to_nat(0u);
v___x_1887_ = l_Lean_Name_reprPrec(v_fst_1881_, v___x_1886_);
v___x_1888_ = lean_box(0);
if (v_isShared_1885_ == 0)
{
lean_ctor_set_tag(v___x_1884_, 1);
lean_ctor_set(v___x_1884_, 1, v___x_1888_);
lean_ctor_set(v___x_1884_, 0, v___x_1887_);
v___x_1890_ = v___x_1884_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; uint8_t v___x_1902_; lean_object* v___x_1903_; 
v___x_1891_ = l_Lean_instReprImportArtifacts_repr___redArg(v_snd_1882_);
v___x_1892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
lean_ctor_set(v___x_1892_, 1, v___x_1890_);
v___x_1893_ = l_List_reverse___redArg(v___x_1892_);
v___x_1894_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_1895_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2_spec__3(v___x_1893_, v___x_1894_);
v___x_1896_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3);
v___x_1897_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__4));
v___x_1898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
lean_ctor_set(v___x_1898_, 1, v___x_1895_);
v___x_1899_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__5));
v___x_1900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1898_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1896_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = 0;
v___x_1903_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set_uint8(v___x_1903_, sizeof(void*)*1, v___x_1902_);
return v___x_1903_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3_spec__5_spec__8(lean_object* v_x_1906_, lean_object* v_x_1907_, lean_object* v_x_1908_){
_start:
{
if (lean_obj_tag(v_x_1908_) == 0)
{
lean_dec(v_x_1906_);
return v_x_1907_;
}
else
{
lean_object* v_head_1909_; lean_object* v_tail_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1920_; 
v_head_1909_ = lean_ctor_get(v_x_1908_, 0);
v_tail_1910_ = lean_ctor_get(v_x_1908_, 1);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_x_1908_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1912_ = v_x_1908_;
v_isShared_1913_ = v_isSharedCheck_1920_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_tail_1910_);
lean_inc(v_head_1909_);
lean_dec(v_x_1908_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1920_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
lean_inc(v_x_1906_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set_tag(v___x_1912_, 5);
lean_ctor_set(v___x_1912_, 1, v_x_1906_);
lean_ctor_set(v___x_1912_, 0, v_x_1907_);
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_x_1907_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_x_1906_);
v___x_1915_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_head_1909_);
v___x_1917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v_x_1907_ = v___x_1917_;
v_x_1908_ = v_tail_1910_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3_spec__5(lean_object* v_x_1921_, lean_object* v_x_1922_, lean_object* v_x_1923_){
_start:
{
if (lean_obj_tag(v_x_1923_) == 0)
{
lean_dec(v_x_1921_);
return v_x_1922_;
}
else
{
lean_object* v_head_1924_; lean_object* v_tail_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1935_; 
v_head_1924_ = lean_ctor_get(v_x_1923_, 0);
v_tail_1925_ = lean_ctor_get(v_x_1923_, 1);
v_isSharedCheck_1935_ = !lean_is_exclusive(v_x_1923_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1927_ = v_x_1923_;
v_isShared_1928_ = v_isSharedCheck_1935_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_tail_1925_);
lean_inc(v_head_1924_);
lean_dec(v_x_1923_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1935_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
lean_inc(v_x_1921_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set_tag(v___x_1927_, 5);
lean_ctor_set(v___x_1927_, 1, v_x_1921_);
lean_ctor_set(v___x_1927_, 0, v_x_1922_);
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_x_1922_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_x_1921_);
v___x_1930_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1931_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_head_1924_);
v___x_1932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1930_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3_spec__5_spec__8(v_x_1921_, v___x_1932_, v_tail_1925_);
return v___x_1933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3(lean_object* v_x_1936_, lean_object* v_x_1937_){
_start:
{
if (lean_obj_tag(v_x_1936_) == 0)
{
lean_object* v___x_1938_; 
lean_dec(v_x_1937_);
v___x_1938_ = lean_box(0);
return v___x_1938_;
}
else
{
lean_object* v_tail_1939_; 
v_tail_1939_ = lean_ctor_get(v_x_1936_, 1);
if (lean_obj_tag(v_tail_1939_) == 0)
{
lean_object* v_head_1940_; lean_object* v___x_1941_; 
lean_dec(v_x_1937_);
v_head_1940_ = lean_ctor_get(v_x_1936_, 0);
lean_inc(v_head_1940_);
lean_dec_ref_known(v_x_1936_, 2);
v___x_1941_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_head_1940_);
return v___x_1941_;
}
else
{
lean_object* v_head_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
lean_inc(v_tail_1939_);
v_head_1942_ = lean_ctor_get(v_x_1936_, 0);
lean_inc(v_head_1942_);
lean_dec_ref_known(v_x_1936_, 2);
v___x_1943_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_head_1942_);
v___x_1944_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3_spec__5(v_x_1937_, v___x_1943_, v_tail_1939_);
return v___x_1944_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = ((lean_object*)(l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__2));
v___x_1950_ = lean_string_length(v___x_1949_);
return v___x_1950_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = lean_obj_once(&l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3, &l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3_once, _init_l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3);
v___x_1952_ = lean_nat_to_int(v___x_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg(lean_object* v_a_1955_){
_start:
{
if (lean_obj_tag(v_a_1955_) == 0)
{
lean_object* v___x_1956_; 
v___x_1956_ = ((lean_object*)(l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__1));
return v___x_1956_;
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; lean_object* v___x_1966_; 
v___x_1957_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_1958_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3(v_a_1955_, v___x_1957_);
v___x_1959_ = lean_obj_once(&l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4, &l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4_once, _init_l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4);
v___x_1960_ = ((lean_object*)(l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__5));
v___x_1961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
lean_ctor_set(v___x_1961_, 1, v___x_1958_);
v___x_1962_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6));
v___x_1963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1961_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
v___x_1964_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1959_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = 0;
v___x_1966_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1966_, 0, v___x_1964_);
lean_ctor_set_uint8(v___x_1966_, sizeof(void*)*1, v___x_1965_);
return v___x_1966_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1(lean_object* v_init_1967_, lean_object* v_x_1968_){
_start:
{
if (lean_obj_tag(v_x_1968_) == 0)
{
lean_object* v_k_1969_; lean_object* v_v_1970_; lean_object* v_l_1971_; lean_object* v_r_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v_k_1969_ = lean_ctor_get(v_x_1968_, 1);
v_v_1970_ = lean_ctor_get(v_x_1968_, 2);
v_l_1971_ = lean_ctor_get(v_x_1968_, 3);
v_r_1972_ = lean_ctor_get(v_x_1968_, 4);
v___x_1973_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1(v_init_1967_, v_r_1972_);
lean_inc(v_v_1970_);
lean_inc(v_k_1969_);
v___x_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1974_, 0, v_k_1969_);
lean_ctor_set(v___x_1974_, 1, v_v_1970_);
v___x_1975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
lean_ctor_set(v___x_1975_, 1, v___x_1973_);
v_init_1967_ = v___x_1975_;
v_x_1968_ = v_l_1971_;
goto _start;
}
else
{
return v_init_1967_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1___boxed(lean_object* v_init_1977_, lean_object* v_x_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1(v_init_1977_, v_x_1978_);
lean_dec(v_x_1978_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5_spec__8_spec__11(lean_object* v_x_1980_, lean_object* v_x_1981_, lean_object* v_x_1982_){
_start:
{
if (lean_obj_tag(v_x_1982_) == 0)
{
lean_dec(v_x_1980_);
return v_x_1981_;
}
else
{
lean_object* v_head_1983_; lean_object* v_tail_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1994_; 
v_head_1983_ = lean_ctor_get(v_x_1982_, 0);
v_tail_1984_ = lean_ctor_get(v_x_1982_, 1);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_x_1982_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1986_ = v_x_1982_;
v_isShared_1987_ = v_isSharedCheck_1994_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_tail_1984_);
lean_inc(v_head_1983_);
lean_dec(v_x_1982_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1994_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
lean_inc(v_x_1980_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set_tag(v___x_1986_, 5);
lean_ctor_set(v___x_1986_, 1, v_x_1980_);
lean_ctor_set(v___x_1986_, 0, v_x_1981_);
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_x_1981_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_x_1980_);
v___x_1989_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = l_Lean_instReprPlugin_repr___redArg(v_head_1983_);
v___x_1991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1989_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v_x_1981_ = v___x_1991_;
v_x_1982_ = v_tail_1984_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5_spec__8(lean_object* v_x_1995_, lean_object* v_x_1996_, lean_object* v_x_1997_){
_start:
{
if (lean_obj_tag(v_x_1997_) == 0)
{
lean_dec(v_x_1995_);
return v_x_1996_;
}
else
{
lean_object* v_head_1998_; lean_object* v_tail_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2009_; 
v_head_1998_ = lean_ctor_get(v_x_1997_, 0);
v_tail_1999_ = lean_ctor_get(v_x_1997_, 1);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_x_1997_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2001_ = v_x_1997_;
v_isShared_2002_ = v_isSharedCheck_2009_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_tail_1999_);
lean_inc(v_head_1998_);
lean_dec(v_x_1997_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2009_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
lean_inc(v_x_1995_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set_tag(v___x_2001_, 5);
lean_ctor_set(v___x_2001_, 1, v_x_1995_);
lean_ctor_set(v___x_2001_, 0, v_x_1996_);
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_x_1996_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_x_1995_);
v___x_2004_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2005_ = l_Lean_instReprPlugin_repr___redArg(v_head_1998_);
v___x_2006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2004_);
lean_ctor_set(v___x_2006_, 1, v___x_2005_);
v___x_2007_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5_spec__8_spec__11(v_x_1995_, v___x_2006_, v_tail_1999_);
return v___x_2007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5(lean_object* v_x_2010_, lean_object* v_x_2011_){
_start:
{
if (lean_obj_tag(v_x_2010_) == 0)
{
lean_object* v___x_2012_; 
lean_dec(v_x_2011_);
v___x_2012_ = lean_box(0);
return v___x_2012_;
}
else
{
lean_object* v_tail_2013_; 
v_tail_2013_ = lean_ctor_get(v_x_2010_, 1);
if (lean_obj_tag(v_tail_2013_) == 0)
{
lean_object* v_head_2014_; lean_object* v___x_2015_; 
lean_dec(v_x_2011_);
v_head_2014_ = lean_ctor_get(v_x_2010_, 0);
lean_inc(v_head_2014_);
lean_dec_ref_known(v_x_2010_, 2);
v___x_2015_ = l_Lean_instReprPlugin_repr___redArg(v_head_2014_);
return v___x_2015_;
}
else
{
lean_object* v_head_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
lean_inc(v_tail_2013_);
v_head_2016_ = lean_ctor_get(v_x_2010_, 0);
lean_inc(v_head_2016_);
lean_dec_ref_known(v_x_2010_, 2);
v___x_2017_ = l_Lean_instReprPlugin_repr___redArg(v_head_2016_);
v___x_2018_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5_spec__8(v_x_2011_, v___x_2017_, v_tail_2013_);
return v___x_2018_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3(lean_object* v_xs_2019_){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2020_ = lean_array_get_size(v_xs_2019_);
v___x_2021_ = lean_unsigned_to_nat(0u);
v___x_2022_ = lean_nat_dec_eq(v___x_2020_, v___x_2021_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2023_ = lean_array_to_list(v_xs_2019_);
v___x_2024_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_2025_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5(v___x_2023_, v___x_2024_);
v___x_2026_ = lean_obj_once(&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4);
v___x_2027_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5));
v___x_2028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
lean_ctor_set(v___x_2028_, 1, v___x_2025_);
v___x_2029_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6));
v___x_2030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2028_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2026_);
lean_ctor_set(v___x_2031_, 1, v___x_2030_);
v___x_2032_ = l_Std_Format_fill(v___x_2031_);
return v___x_2032_;
}
else
{
lean_object* v___x_2033_; 
lean_dec_ref(v_xs_2019_);
v___x_2033_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8));
return v___x_2033_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprModuleSetup_repr_spec__0(lean_object* v_x_2034_, lean_object* v_x_2035_){
_start:
{
if (lean_obj_tag(v_x_2034_) == 0)
{
lean_object* v___x_2036_; 
v___x_2036_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__1));
return v___x_2036_;
}
else
{
lean_object* v_val_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v_val_2037_ = lean_ctor_get(v_x_2034_, 0);
lean_inc(v_val_2037_);
lean_dec_ref_known(v_x_2034_, 1);
v___x_2038_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__3));
v___x_2039_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0(v_val_2037_);
v___x_2040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2038_);
lean_ctor_set(v___x_2040_, 1, v___x_2039_);
v___x_2041_ = l_Repr_addAppParen(v___x_2040_, v_x_2035_);
return v___x_2041_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprModuleSetup_repr_spec__0___boxed(lean_object* v_x_2042_, lean_object* v_x_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Option_repr___at___00Lean_instReprModuleSetup_repr_spec__0(v_x_2042_, v_x_2043_);
lean_dec(v_x_2043_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleSetup_repr___redArg(lean_object* v_x_2075_){
_start:
{
lean_object* v_name_2076_; lean_object* v_package_x3f_2077_; uint8_t v_isModule_2078_; lean_object* v_imports_x3f_2079_; lean_object* v_importArts_2080_; lean_object* v_dynlibs_2081_; lean_object* v_plugins_2082_; lean_object* v_options_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v_name_2076_ = lean_ctor_get(v_x_2075_, 0);
lean_inc(v_name_2076_);
v_package_x3f_2077_ = lean_ctor_get(v_x_2075_, 1);
lean_inc(v_package_x3f_2077_);
v_isModule_2078_ = lean_ctor_get_uint8(v_x_2075_, sizeof(void*)*7);
v_imports_x3f_2079_ = lean_ctor_get(v_x_2075_, 2);
lean_inc(v_imports_x3f_2079_);
v_importArts_2080_ = lean_ctor_get(v_x_2075_, 3);
lean_inc(v_importArts_2080_);
v_dynlibs_2081_ = lean_ctor_get(v_x_2075_, 4);
lean_inc_ref(v_dynlibs_2081_);
v_plugins_2082_ = lean_ctor_get(v_x_2075_, 5);
lean_inc_ref(v_plugins_2082_);
v_options_2083_ = lean_ctor_get(v_x_2075_, 6);
lean_inc(v_options_2083_);
lean_dec_ref(v_x_2075_);
v___x_2084_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__5));
v___x_2085_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__3));
v___x_2086_ = lean_obj_once(&l_Lean_instReprPlugin_repr___redArg___closed__4, &l_Lean_instReprPlugin_repr___redArg___closed__4_once, _init_l_Lean_instReprPlugin_repr___redArg___closed__4);
v___x_2087_ = lean_unsigned_to_nat(0u);
v___x_2088_ = l_Lean_Name_reprPrec(v_name_2076_, v___x_2087_);
v___x_2089_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2086_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
v___x_2090_ = 0;
v___x_2091_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2091_, 0, v___x_2089_);
lean_ctor_set_uint8(v___x_2091_, sizeof(void*)*1, v___x_2090_);
v___x_2092_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2085_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
v___x_2093_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__9));
v___x_2094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2092_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = lean_box(1);
v___x_2096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2094_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v___x_2097_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__5));
v___x_2098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2096_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
lean_ctor_set(v___x_2099_, 1, v___x_2084_);
v___x_2100_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__7, &l_Lean_instReprModuleHeader_repr___redArg___closed__7_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__7);
v___x_2101_ = l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0(v_package_x3f_2077_, v___x_2087_);
v___x_2102_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2100_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
v___x_2103_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
lean_ctor_set_uint8(v___x_2103_, sizeof(void*)*1, v___x_2090_);
v___x_2104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2099_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v___x_2105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
lean_ctor_set(v___x_2105_, 1, v___x_2093_);
v___x_2106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
lean_ctor_set(v___x_2106_, 1, v___x_2095_);
v___x_2107_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__6));
v___x_2108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2106_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
v___x_2109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
lean_ctor_set(v___x_2109_, 1, v___x_2084_);
v___x_2110_ = l_Bool_repr___redArg(v_isModule_2078_);
v___x_2111_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2100_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
v___x_2112_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
lean_ctor_set_uint8(v___x_2112_, sizeof(void*)*1, v___x_2090_);
v___x_2113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2109_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
lean_ctor_set(v___x_2114_, 1, v___x_2093_);
v___x_2115_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_ctor_set(v___x_2115_, 1, v___x_2095_);
v___x_2116_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__7));
v___x_2117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2115_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v___x_2118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v___x_2084_);
v___x_2119_ = l_Option_repr___at___00Lean_instReprModuleSetup_repr_spec__0(v_imports_x3f_2079_, v___x_2087_);
v___x_2120_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2100_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
v___x_2121_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
lean_ctor_set_uint8(v___x_2121_, sizeof(void*)*1, v___x_2090_);
v___x_2122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2118_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
lean_ctor_set(v___x_2123_, 1, v___x_2093_);
v___x_2124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
lean_ctor_set(v___x_2124_, 1, v___x_2095_);
v___x_2125_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__9));
v___x_2126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2124_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_ctor_set(v___x_2127_, 1, v___x_2084_);
v___x_2128_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__15, &l_Lean_instReprImport_repr___redArg___closed__15_once, _init_l_Lean_instReprImport_repr___redArg___closed__15);
v___x_2129_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__11));
v___x_2130_ = lean_box(0);
v___x_2131_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1(v___x_2130_, v_importArts_2080_);
lean_dec(v_importArts_2080_);
v___x_2132_ = l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg(v___x_2131_);
v___x_2133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2129_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = l_Repr_addAppParen(v___x_2133_, v___x_2087_);
v___x_2135_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2128_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
v___x_2136_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
lean_ctor_set_uint8(v___x_2136_, sizeof(void*)*1, v___x_2090_);
v___x_2137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2127_);
lean_ctor_set(v___x_2137_, 1, v___x_2136_);
v___x_2138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2137_);
lean_ctor_set(v___x_2138_, 1, v___x_2093_);
v___x_2139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2138_);
lean_ctor_set(v___x_2139_, 1, v___x_2095_);
v___x_2140_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__13));
v___x_2141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2139_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
lean_ctor_set(v___x_2142_, 1, v___x_2084_);
v___x_2143_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__4, &l_Lean_instReprModuleHeader_repr___redArg___closed__4_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__4);
v___x_2144_ = l_Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0(v_dynlibs_2081_);
v___x_2145_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2143_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
lean_ctor_set_uint8(v___x_2146_, sizeof(void*)*1, v___x_2090_);
v___x_2147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2142_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
lean_ctor_set(v___x_2148_, 1, v___x_2093_);
v___x_2149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2148_);
lean_ctor_set(v___x_2149_, 1, v___x_2095_);
v___x_2150_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__15));
v___x_2151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2149_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v___x_2152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
lean_ctor_set(v___x_2152_, 1, v___x_2084_);
v___x_2153_ = l_Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3(v_plugins_2082_);
v___x_2154_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2143_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
lean_ctor_set_uint8(v___x_2155_, sizeof(void*)*1, v___x_2090_);
v___x_2156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2152_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
lean_ctor_set(v___x_2157_, 1, v___x_2093_);
v___x_2158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
lean_ctor_set(v___x_2158_, 1, v___x_2095_);
v___x_2159_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__17));
v___x_2160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2158_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
lean_ctor_set(v___x_2161_, 1, v___x_2084_);
v___x_2162_ = l_Lean_instReprLeanOptions_repr___redArg(v_options_2083_);
lean_dec(v_options_2083_);
v___x_2163_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2143_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
lean_ctor_set_uint8(v___x_2164_, sizeof(void*)*1, v___x_2090_);
v___x_2165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2161_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__20, &l_Lean_instReprImport_repr___redArg___closed__20_once, _init_l_Lean_instReprImport_repr___redArg___closed__20);
v___x_2167_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__21));
v___x_2168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
lean_ctor_set(v___x_2168_, 1, v___x_2165_);
v___x_2169_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__22));
v___x_2170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2168_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
v___x_2171_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2166_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
v___x_2172_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
lean_ctor_set_uint8(v___x_2172_, sizeof(void*)*1, v___x_2090_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleSetup_repr(lean_object* v_x_2173_, lean_object* v_prec_2174_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Lean_instReprModuleSetup_repr___redArg(v_x_2173_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleSetup_repr___boxed(lean_object* v_x_2176_, lean_object* v_prec_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_instReprModuleSetup_repr(v_x_2176_, v_prec_2177_);
lean_dec(v_prec_2177_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2(lean_object* v_a_2179_, lean_object* v_n_2180_){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg(v_a_2179_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___boxed(lean_object* v_a_2182_, lean_object* v_n_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2(v_a_2182_, v_n_2183_);
lean_dec(v_n_2183_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2(lean_object* v_x_2185_, lean_object* v_x_2186_){
_start:
{
lean_object* v___x_2187_; 
v___x_2187_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_x_2185_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___boxed(lean_object* v_x_2188_, lean_object* v_x_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2(v_x_2188_, v_x_2189_);
lean_dec(v_x_2189_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__5(size_t v_sz_2201_, size_t v_i_2202_, lean_object* v_bs_2203_){
_start:
{
uint8_t v___x_2204_; 
v___x_2204_ = lean_usize_dec_lt(v_i_2202_, v_sz_2201_);
if (v___x_2204_ == 0)
{
return v_bs_2203_;
}
else
{
lean_object* v_v_2205_; lean_object* v___x_2206_; lean_object* v_bs_x27_2207_; lean_object* v___x_2208_; size_t v___x_2209_; size_t v___x_2210_; lean_object* v___x_2211_; 
v_v_2205_ = lean_array_uget(v_bs_2203_, v_i_2202_);
v___x_2206_ = lean_unsigned_to_nat(0u);
v_bs_x27_2207_ = lean_array_uset(v_bs_2203_, v_i_2202_, v___x_2206_);
v___x_2208_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2208_, 0, v_v_2205_);
v___x_2209_ = ((size_t)1ULL);
v___x_2210_ = lean_usize_add(v_i_2202_, v___x_2209_);
v___x_2211_ = lean_array_uset(v_bs_x27_2207_, v_i_2202_, v___x_2208_);
v_i_2202_ = v___x_2210_;
v_bs_2203_ = v___x_2211_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__5___boxed(lean_object* v_sz_2213_, lean_object* v_i_2214_, lean_object* v_bs_2215_){
_start:
{
size_t v_sz_boxed_2216_; size_t v_i_boxed_2217_; lean_object* v_res_2218_; 
v_sz_boxed_2216_ = lean_unbox_usize(v_sz_2213_);
lean_dec(v_sz_2213_);
v_i_boxed_2217_ = lean_unbox_usize(v_i_2214_);
lean_dec(v_i_2214_);
v_res_2218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__5(v_sz_boxed_2216_, v_i_boxed_2217_, v_bs_2215_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2(lean_object* v_a_2219_){
_start:
{
size_t v_sz_2220_; size_t v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v_sz_2220_ = lean_array_size(v_a_2219_);
v___x_2221_ = ((size_t)0ULL);
v___x_2222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__5(v_sz_2220_, v___x_2221_, v_a_2219_);
v___x_2223_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2(size_t v_sz_2224_, size_t v_i_2225_, lean_object* v_bs_2226_){
_start:
{
uint8_t v___x_2227_; 
v___x_2227_ = lean_usize_dec_lt(v_i_2225_, v_sz_2224_);
if (v___x_2227_ == 0)
{
return v_bs_2226_;
}
else
{
lean_object* v_v_2228_; lean_object* v___x_2229_; lean_object* v_bs_x27_2230_; lean_object* v___x_2231_; size_t v___x_2232_; size_t v___x_2233_; lean_object* v___x_2234_; 
v_v_2228_ = lean_array_uget(v_bs_2226_, v_i_2225_);
v___x_2229_ = lean_unsigned_to_nat(0u);
v_bs_x27_2230_ = lean_array_uset(v_bs_2226_, v_i_2225_, v___x_2229_);
v___x_2231_ = l_Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2(v_v_2228_);
v___x_2232_ = ((size_t)1ULL);
v___x_2233_ = lean_usize_add(v_i_2225_, v___x_2232_);
v___x_2234_ = lean_array_uset(v_bs_x27_2230_, v_i_2225_, v___x_2231_);
v_i_2225_ = v___x_2233_;
v_bs_2226_ = v___x_2234_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2236_, lean_object* v_i_2237_, lean_object* v_bs_2238_){
_start:
{
size_t v_sz_boxed_2239_; size_t v_i_boxed_2240_; lean_object* v_res_2241_; 
v_sz_boxed_2239_ = lean_unbox_usize(v_sz_2236_);
lean_dec(v_sz_2236_);
v_i_boxed_2240_ = lean_unbox_usize(v_i_2237_);
lean_dec(v_i_2237_);
v_res_2241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2(v_sz_boxed_2239_, v_i_boxed_2240_, v_bs_2238_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1(lean_object* v_a_2242_){
_start:
{
size_t v_sz_2243_; size_t v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v_sz_2243_ = lean_array_size(v_a_2242_);
v___x_2244_ = ((size_t)0ULL);
v___x_2245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2(v_sz_2243_, v___x_2244_, v_a_2242_);
v___x_2246_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4___redArg(lean_object* v_msg_2247_){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = lean_box(1);
v___x_2249_ = lean_panic_fn_borrowed(v___x_2248_, v_msg_2247_);
return v___x_2249_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2253_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__2));
v___x_2254_ = lean_unsigned_to_nat(35u);
v___x_2255_ = lean_unsigned_to_nat(182u);
v___x_2256_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__1));
v___x_2257_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__0));
v___x_2258_ = l_mkPanicMessageWithDecl(v___x_2257_, v___x_2256_, v___x_2255_, v___x_2254_, v___x_2253_);
return v___x_2258_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2259_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__2));
v___x_2260_ = lean_unsigned_to_nat(21u);
v___x_2261_ = lean_unsigned_to_nat(183u);
v___x_2262_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__1));
v___x_2263_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__0));
v___x_2264_ = l_mkPanicMessageWithDecl(v___x_2263_, v___x_2262_, v___x_2261_, v___x_2260_, v___x_2259_);
return v___x_2264_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2267_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__6));
v___x_2268_ = lean_unsigned_to_nat(35u);
v___x_2269_ = lean_unsigned_to_nat(276u);
v___x_2270_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__5));
v___x_2271_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__0));
v___x_2272_ = l_mkPanicMessageWithDecl(v___x_2271_, v___x_2270_, v___x_2269_, v___x_2268_, v___x_2267_);
return v___x_2272_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2273_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__6));
v___x_2274_ = lean_unsigned_to_nat(21u);
v___x_2275_ = lean_unsigned_to_nat(277u);
v___x_2276_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__5));
v___x_2277_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__0));
v___x_2278_ = l_mkPanicMessageWithDecl(v___x_2277_, v___x_2276_, v___x_2275_, v___x_2274_, v___x_2273_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg(lean_object* v_k_2279_, lean_object* v_v_2280_, lean_object* v_t_2281_){
_start:
{
if (lean_obj_tag(v_t_2281_) == 0)
{
lean_object* v_size_2282_; lean_object* v_k_2283_; lean_object* v_v_2284_; lean_object* v_l_2285_; lean_object* v_r_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2642_; 
v_size_2282_ = lean_ctor_get(v_t_2281_, 0);
v_k_2283_ = lean_ctor_get(v_t_2281_, 1);
v_v_2284_ = lean_ctor_get(v_t_2281_, 2);
v_l_2285_ = lean_ctor_get(v_t_2281_, 3);
v_r_2286_ = lean_ctor_get(v_t_2281_, 4);
v_isSharedCheck_2642_ = !lean_is_exclusive(v_t_2281_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2288_ = v_t_2281_;
v_isShared_2289_ = v_isSharedCheck_2642_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_r_2286_);
lean_inc(v_l_2285_);
lean_inc(v_v_2284_);
lean_inc(v_k_2283_);
lean_inc(v_size_2282_);
lean_dec(v_t_2281_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2642_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
uint8_t v___x_2290_; 
v___x_2290_ = lean_string_compare(v_k_2279_, v_k_2283_);
switch(v___x_2290_)
{
case 0:
{
lean_object* v___x_2291_; 
lean_dec(v_size_2282_);
v___x_2291_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg(v_k_2279_, v_v_2280_, v_l_2285_);
if (lean_obj_tag(v_r_2286_) == 0)
{
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_size_2292_; lean_object* v_size_2293_; lean_object* v_k_2294_; lean_object* v_v_2295_; lean_object* v_l_2296_; lean_object* v_r_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; uint8_t v___x_2300_; 
v_size_2292_ = lean_ctor_get(v_r_2286_, 0);
v_size_2293_ = lean_ctor_get(v___x_2291_, 0);
v_k_2294_ = lean_ctor_get(v___x_2291_, 1);
v_v_2295_ = lean_ctor_get(v___x_2291_, 2);
v_l_2296_ = lean_ctor_get(v___x_2291_, 3);
v_r_2297_ = lean_ctor_get(v___x_2291_, 4);
lean_inc(v_r_2297_);
v___x_2298_ = lean_unsigned_to_nat(3u);
v___x_2299_ = lean_nat_mul(v___x_2298_, v_size_2292_);
v___x_2300_ = lean_nat_dec_lt(v___x_2299_, v_size_2293_);
lean_dec(v___x_2299_);
if (v___x_2300_ == 0)
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2305_; 
lean_dec(v_r_2297_);
v___x_2301_ = lean_unsigned_to_nat(1u);
v___x_2302_ = lean_nat_add(v___x_2301_, v_size_2293_);
v___x_2303_ = lean_nat_add(v___x_2302_, v_size_2292_);
lean_dec(v___x_2302_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 3, v___x_2291_);
lean_ctor_set(v___x_2288_, 0, v___x_2303_);
v___x_2305_ = v___x_2288_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
lean_ctor_set(v_reuseFailAlloc_2306_, 1, v_k_2283_);
lean_ctor_set(v_reuseFailAlloc_2306_, 2, v_v_2284_);
lean_ctor_set(v_reuseFailAlloc_2306_, 3, v___x_2291_);
lean_ctor_set(v_reuseFailAlloc_2306_, 4, v_r_2286_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
else
{
lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2378_; 
lean_inc(v_l_2296_);
lean_inc(v_v_2295_);
lean_inc(v_k_2294_);
lean_inc(v_size_2293_);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2378_ == 0)
{
lean_object* v_unused_2379_; lean_object* v_unused_2380_; lean_object* v_unused_2381_; lean_object* v_unused_2382_; lean_object* v_unused_2383_; 
v_unused_2379_ = lean_ctor_get(v___x_2291_, 4);
lean_dec(v_unused_2379_);
v_unused_2380_ = lean_ctor_get(v___x_2291_, 3);
lean_dec(v_unused_2380_);
v_unused_2381_ = lean_ctor_get(v___x_2291_, 2);
lean_dec(v_unused_2381_);
v_unused_2382_ = lean_ctor_get(v___x_2291_, 1);
lean_dec(v_unused_2382_);
v_unused_2383_ = lean_ctor_get(v___x_2291_, 0);
lean_dec(v_unused_2383_);
v___x_2308_ = v___x_2291_;
v_isShared_2309_ = v_isSharedCheck_2378_;
goto v_resetjp_2307_;
}
else
{
lean_dec(v___x_2291_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2378_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
if (lean_obj_tag(v_l_2296_) == 0)
{
if (lean_obj_tag(v_r_2297_) == 0)
{
lean_object* v_size_2310_; lean_object* v_size_2311_; lean_object* v_k_2312_; lean_object* v_v_2313_; lean_object* v_l_2314_; lean_object* v_r_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; 
v_size_2310_ = lean_ctor_get(v_l_2296_, 0);
v_size_2311_ = lean_ctor_get(v_r_2297_, 0);
v_k_2312_ = lean_ctor_get(v_r_2297_, 1);
v_v_2313_ = lean_ctor_get(v_r_2297_, 2);
v_l_2314_ = lean_ctor_get(v_r_2297_, 3);
v_r_2315_ = lean_ctor_get(v_r_2297_, 4);
v___x_2316_ = lean_unsigned_to_nat(2u);
v___x_2317_ = lean_nat_mul(v___x_2316_, v_size_2310_);
v___x_2318_ = lean_nat_dec_lt(v_size_2311_, v___x_2317_);
lean_dec(v___x_2317_);
if (v___x_2318_ == 0)
{
lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2348_; 
lean_inc(v_r_2315_);
lean_inc(v_l_2314_);
lean_inc(v_v_2313_);
lean_inc(v_k_2312_);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_r_2297_);
if (v_isSharedCheck_2348_ == 0)
{
lean_object* v_unused_2349_; lean_object* v_unused_2350_; lean_object* v_unused_2351_; lean_object* v_unused_2352_; lean_object* v_unused_2353_; 
v_unused_2349_ = lean_ctor_get(v_r_2297_, 4);
lean_dec(v_unused_2349_);
v_unused_2350_ = lean_ctor_get(v_r_2297_, 3);
lean_dec(v_unused_2350_);
v_unused_2351_ = lean_ctor_get(v_r_2297_, 2);
lean_dec(v_unused_2351_);
v_unused_2352_ = lean_ctor_get(v_r_2297_, 1);
lean_dec(v_unused_2352_);
v_unused_2353_ = lean_ctor_get(v_r_2297_, 0);
lean_dec(v_unused_2353_);
v___x_2320_ = v_r_2297_;
v_isShared_2321_ = v_isSharedCheck_2348_;
goto v_resetjp_2319_;
}
else
{
lean_dec(v_r_2297_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2348_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___x_2336_; lean_object* v___y_2338_; 
v___x_2322_ = lean_unsigned_to_nat(1u);
v___x_2323_ = lean_nat_add(v___x_2322_, v_size_2293_);
lean_dec(v_size_2293_);
v___x_2324_ = lean_nat_add(v___x_2323_, v_size_2292_);
lean_dec(v___x_2323_);
v___x_2336_ = lean_nat_add(v___x_2322_, v_size_2310_);
if (lean_obj_tag(v_l_2314_) == 0)
{
lean_object* v_size_2346_; 
v_size_2346_ = lean_ctor_get(v_l_2314_, 0);
lean_inc(v_size_2346_);
v___y_2338_ = v_size_2346_;
goto v___jp_2337_;
}
else
{
lean_object* v___x_2347_; 
v___x_2347_ = lean_unsigned_to_nat(0u);
v___y_2338_ = v___x_2347_;
goto v___jp_2337_;
}
v___jp_2325_:
{
lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2329_ = lean_nat_add(v___y_2326_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec(v___y_2326_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 4, v_r_2286_);
lean_ctor_set(v___x_2320_, 3, v_r_2315_);
lean_ctor_set(v___x_2320_, 2, v_v_2284_);
lean_ctor_set(v___x_2320_, 1, v_k_2283_);
lean_ctor_set(v___x_2320_, 0, v___x_2329_);
v___x_2331_ = v___x_2320_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2329_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_k_2283_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_v_2284_);
lean_ctor_set(v_reuseFailAlloc_2335_, 3, v_r_2315_);
lean_ctor_set(v_reuseFailAlloc_2335_, 4, v_r_2286_);
v___x_2331_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2333_; 
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 4, v___x_2331_);
lean_ctor_set(v___x_2308_, 3, v___y_2327_);
lean_ctor_set(v___x_2308_, 2, v_v_2313_);
lean_ctor_set(v___x_2308_, 1, v_k_2312_);
lean_ctor_set(v___x_2308_, 0, v___x_2324_);
v___x_2333_ = v___x_2308_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2324_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_k_2312_);
lean_ctor_set(v_reuseFailAlloc_2334_, 2, v_v_2313_);
lean_ctor_set(v_reuseFailAlloc_2334_, 3, v___y_2327_);
lean_ctor_set(v_reuseFailAlloc_2334_, 4, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
v___jp_2337_:
{
lean_object* v___x_2339_; lean_object* v___x_2341_; 
v___x_2339_ = lean_nat_add(v___x_2336_, v___y_2338_);
lean_dec(v___y_2338_);
lean_dec(v___x_2336_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 4, v_l_2314_);
lean_ctor_set(v___x_2288_, 3, v_l_2296_);
lean_ctor_set(v___x_2288_, 2, v_v_2295_);
lean_ctor_set(v___x_2288_, 1, v_k_2294_);
lean_ctor_set(v___x_2288_, 0, v___x_2339_);
v___x_2341_ = v___x_2288_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2339_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v_k_2294_);
lean_ctor_set(v_reuseFailAlloc_2345_, 2, v_v_2295_);
lean_ctor_set(v_reuseFailAlloc_2345_, 3, v_l_2296_);
lean_ctor_set(v_reuseFailAlloc_2345_, 4, v_l_2314_);
v___x_2341_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
lean_object* v___x_2342_; 
v___x_2342_ = lean_nat_add(v___x_2322_, v_size_2292_);
if (lean_obj_tag(v_r_2315_) == 0)
{
lean_object* v_size_2343_; 
v_size_2343_ = lean_ctor_get(v_r_2315_, 0);
lean_inc(v_size_2343_);
v___y_2326_ = v___x_2342_;
v___y_2327_ = v___x_2341_;
v___y_2328_ = v_size_2343_;
goto v___jp_2325_;
}
else
{
lean_object* v___x_2344_; 
v___x_2344_ = lean_unsigned_to_nat(0u);
v___y_2326_ = v___x_2342_;
v___y_2327_ = v___x_2341_;
v___y_2328_ = v___x_2344_;
goto v___jp_2325_;
}
}
}
}
}
else
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2360_; 
lean_del_object(v___x_2288_);
v___x_2354_ = lean_unsigned_to_nat(1u);
v___x_2355_ = lean_nat_add(v___x_2354_, v_size_2293_);
lean_dec(v_size_2293_);
v___x_2356_ = lean_nat_add(v___x_2355_, v_size_2292_);
lean_dec(v___x_2355_);
v___x_2357_ = lean_nat_add(v___x_2354_, v_size_2292_);
v___x_2358_ = lean_nat_add(v___x_2357_, v_size_2311_);
lean_dec(v___x_2357_);
lean_inc_ref(v_r_2286_);
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 4, v_r_2286_);
lean_ctor_set(v___x_2308_, 3, v_r_2297_);
lean_ctor_set(v___x_2308_, 2, v_v_2284_);
lean_ctor_set(v___x_2308_, 1, v_k_2283_);
lean_ctor_set(v___x_2308_, 0, v___x_2358_);
v___x_2360_ = v___x_2308_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2358_);
lean_ctor_set(v_reuseFailAlloc_2373_, 1, v_k_2283_);
lean_ctor_set(v_reuseFailAlloc_2373_, 2, v_v_2284_);
lean_ctor_set(v_reuseFailAlloc_2373_, 3, v_r_2297_);
lean_ctor_set(v_reuseFailAlloc_2373_, 4, v_r_2286_);
v___x_2360_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
v_isSharedCheck_2367_ = !lean_is_exclusive(v_r_2286_);
if (v_isSharedCheck_2367_ == 0)
{
lean_object* v_unused_2368_; lean_object* v_unused_2369_; lean_object* v_unused_2370_; lean_object* v_unused_2371_; lean_object* v_unused_2372_; 
v_unused_2368_ = lean_ctor_get(v_r_2286_, 4);
lean_dec(v_unused_2368_);
v_unused_2369_ = lean_ctor_get(v_r_2286_, 3);
lean_dec(v_unused_2369_);
v_unused_2370_ = lean_ctor_get(v_r_2286_, 2);
lean_dec(v_unused_2370_);
v_unused_2371_ = lean_ctor_get(v_r_2286_, 1);
lean_dec(v_unused_2371_);
v_unused_2372_ = lean_ctor_get(v_r_2286_, 0);
lean_dec(v_unused_2372_);
v___x_2362_ = v_r_2286_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_dec(v_r_2286_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 4, v___x_2360_);
lean_ctor_set(v___x_2362_, 3, v_l_2296_);
lean_ctor_set(v___x_2362_, 2, v_v_2295_);
lean_ctor_set(v___x_2362_, 1, v_k_2294_);
lean_ctor_set(v___x_2362_, 0, v___x_2356_);
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2356_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v_k_2294_);
lean_ctor_set(v_reuseFailAlloc_2366_, 2, v_v_2295_);
lean_ctor_set(v_reuseFailAlloc_2366_, 3, v_l_2296_);
lean_ctor_set(v_reuseFailAlloc_2366_, 4, v___x_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
}
else
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
lean_dec_ref_known(v_l_2296_, 5);
lean_del_object(v___x_2308_);
lean_dec(v_v_2295_);
lean_dec(v_k_2294_);
lean_dec(v_size_2293_);
lean_dec_ref_known(v_r_2286_, 5);
lean_del_object(v___x_2288_);
lean_dec(v_v_2284_);
lean_dec(v_k_2283_);
v___x_2374_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__3);
v___x_2375_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4___redArg(v___x_2374_);
return v___x_2375_;
}
}
else
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
lean_del_object(v___x_2308_);
lean_dec(v_r_2297_);
lean_dec(v_v_2295_);
lean_dec(v_k_2294_);
lean_dec(v_size_2293_);
lean_dec_ref_known(v_r_2286_, 5);
lean_del_object(v___x_2288_);
lean_dec(v_v_2284_);
lean_dec(v_k_2283_);
v___x_2376_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__4);
v___x_2377_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4___redArg(v___x_2376_);
return v___x_2377_;
}
}
}
}
else
{
lean_object* v_size_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2388_; 
v_size_2384_ = lean_ctor_get(v_r_2286_, 0);
v___x_2385_ = lean_unsigned_to_nat(1u);
v___x_2386_ = lean_nat_add(v___x_2385_, v_size_2384_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 3, v___x_2291_);
lean_ctor_set(v___x_2288_, 0, v___x_2386_);
v___x_2388_ = v___x_2288_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v_k_2283_);
lean_ctor_set(v_reuseFailAlloc_2389_, 2, v_v_2284_);
lean_ctor_set(v_reuseFailAlloc_2389_, 3, v___x_2291_);
lean_ctor_set(v_reuseFailAlloc_2389_, 4, v_r_2286_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
else
{
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_l_2390_; 
v_l_2390_ = lean_ctor_get(v___x_2291_, 3);
if (lean_obj_tag(v_l_2390_) == 0)
{
lean_object* v_r_2391_; 
lean_inc_ref(v_l_2390_);
v_r_2391_ = lean_ctor_get(v___x_2291_, 4);
lean_inc(v_r_2391_);
if (lean_obj_tag(v_r_2391_) == 0)
{
lean_object* v_size_2392_; lean_object* v_k_2393_; lean_object* v_v_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2408_; 
v_size_2392_ = lean_ctor_get(v___x_2291_, 0);
v_k_2393_ = lean_ctor_get(v___x_2291_, 1);
v_v_2394_ = lean_ctor_get(v___x_2291_, 2);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2408_ == 0)
{
lean_object* v_unused_2409_; lean_object* v_unused_2410_; 
v_unused_2409_ = lean_ctor_get(v___x_2291_, 4);
lean_dec(v_unused_2409_);
v_unused_2410_ = lean_ctor_get(v___x_2291_, 3);
lean_dec(v_unused_2410_);
v___x_2396_ = v___x_2291_;
v_isShared_2397_ = v_isSharedCheck_2408_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_v_2394_);
lean_inc(v_k_2393_);
lean_inc(v_size_2392_);
lean_dec(v___x_2291_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2408_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v_size_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2403_; 
v_size_2398_ = lean_ctor_get(v_r_2391_, 0);
v___x_2399_ = lean_unsigned_to_nat(1u);
v___x_2400_ = lean_nat_add(v___x_2399_, v_size_2392_);
lean_dec(v_size_2392_);
v___x_2401_ = lean_nat_add(v___x_2399_, v_size_2398_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 4, v_r_2286_);
lean_ctor_set(v___x_2396_, 3, v_r_2391_);
lean_ctor_set(v___x_2396_, 2, v_v_2284_);
lean_ctor_set(v___x_2396_, 1, v_k_2283_);
lean_ctor_set(v___x_2396_, 0, v___x_2401_);
v___x_2403_ = v___x_2396_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v_k_2283_);
lean_ctor_set(v_reuseFailAlloc_2407_, 2, v_v_2284_);
lean_ctor_set(v_reuseFailAlloc_2407_, 3, v_r_2391_);
lean_ctor_set(v_reuseFailAlloc_2407_, 4, v_r_2286_);
v___x_2403_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2405_; 
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 4, v___x_2403_);
lean_ctor_set(v___x_2288_, 3, v_l_2390_);
lean_ctor_set(v___x_2288_, 2, v_v_2394_);
lean_ctor_set(v___x_2288_, 1, v_k_2393_);
lean_ctor_set(v___x_2288_, 0, v___x_2400_);
v___x_2405_ = v___x_2288_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2400_);
lean_ctor_set(v_reuseFailAlloc_2406_, 1, v_k_2393_);
lean_ctor_set(v_reuseFailAlloc_2406_, 2, v_v_2394_);
lean_ctor_set(v_reuseFailAlloc_2406_, 3, v_l_2390_);
lean_ctor_set(v_reuseFailAlloc_2406_, 4, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
else
{
lean_object* v_k_2411_; lean_object* v_v_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2424_; 
v_k_2411_ = lean_ctor_get(v___x_2291_, 1);
v_v_2412_ = lean_ctor_get(v___x_2291_, 2);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2424_ == 0)
{
lean_object* v_unused_2425_; lean_object* v_unused_2426_; lean_object* v_unused_2427_; 
v_unused_2425_ = lean_ctor_get(v___x_2291_, 4);
lean_dec(v_unused_2425_);
v_unused_2426_ = lean_ctor_get(v___x_2291_, 3);
lean_dec(v_unused_2426_);
v_unused_2427_ = lean_ctor_get(v___x_2291_, 0);
lean_dec(v_unused_2427_);
v___x_2414_ = v___x_2291_;
v_isShared_2415_ = v_isSharedCheck_2424_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_v_2412_);
lean_inc(v_k_2411_);
lean_dec(v___x_2291_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2424_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2419_; 
v___x_2416_ = lean_unsigned_to_nat(3u);
v___x_2417_ = lean_unsigned_to_nat(1u);
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 3, v_r_2391_);
lean_ctor_set(v___x_2414_, 2, v_v_2284_);
lean_ctor_set(v___x_2414_, 1, v_k_2283_);
lean_ctor_set(v___x_2414_, 0, v___x_2417_);
v___x_2419_ = v___x_2414_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2417_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_k_2283_);
lean_ctor_set(v_reuseFailAlloc_2423_, 2, v_v_2284_);
lean_ctor_set(v_reuseFailAlloc_2423_, 3, v_r_2391_);
lean_ctor_set(v_reuseFailAlloc_2423_, 4, v_r_2391_);
v___x_2419_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
lean_object* v___x_2421_; 
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 4, v___x_2419_);
lean_ctor_set(v___x_2288_, 3, v_l_2390_);
lean_ctor_set(v___x_2288_, 2, v_v_2412_);
lean_ctor_set(v___x_2288_, 1, v_k_2411_);
lean_ctor_set(v___x_2288_, 0, v___x_2416_);
v___x_2421_ = v___x_2288_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2416_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_k_2411_);
lean_ctor_set(v_reuseFailAlloc_2422_, 2, v_v_2412_);
lean_ctor_set(v_reuseFailAlloc_2422_, 3, v_l_2390_);
lean_ctor_set(v_reuseFailAlloc_2422_, 4, v___x_2419_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
}
else
{
lean_object* v_r_2428_; 
v_r_2428_ = lean_ctor_get(v___x_2291_, 4);
lean_inc(v_r_2428_);
if (lean_obj_tag(v_r_2428_) == 0)
{
lean_object* v_k_2429_; lean_object* v_v_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2454_; 
lean_inc(v_l_2390_);
v_k_2429_ = lean_ctor_get(v___x_2291_, 1);
v_v_2430_ = lean_ctor_get(v___x_2291_, 2);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2454_ == 0)
{
lean_object* v_unused_2455_; lean_object* v_unused_2456_; lean_object* v_unused_2457_; 
v_unused_2455_ = lean_ctor_get(v___x_2291_, 4);
lean_dec(v_unused_2455_);
v_unused_2456_ = lean_ctor_get(v___x_2291_, 3);
lean_dec(v_unused_2456_);
v_unused_2457_ = lean_ctor_get(v___x_2291_, 0);
lean_dec(v_unused_2457_);
v___x_2432_ = v___x_2291_;
v_isShared_2433_ = v_isSharedCheck_2454_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_v_2430_);
lean_inc(v_k_2429_);
lean_dec(v___x_2291_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2454_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v_k_2434_; lean_object* v_v_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2450_; 
v_k_2434_ = lean_ctor_get(v_r_2428_, 1);
v_v_2435_ = lean_ctor_get(v_r_2428_, 2);
v_isSharedCheck_2450_ = !lean_is_exclusive(v_r_2428_);
if (v_isSharedCheck_2450_ == 0)
{
lean_object* v_unused_2451_; lean_object* v_unused_2452_; lean_object* v_unused_2453_; 
v_unused_2451_ = lean_ctor_get(v_r_2428_, 4);
lean_dec(v_unused_2451_);
v_unused_2452_ = lean_ctor_get(v_r_2428_, 3);
lean_dec(v_unused_2452_);
v_unused_2453_ = lean_ctor_get(v_r_2428_, 0);
lean_dec(v_unused_2453_);
v___x_2437_ = v_r_2428_;
v_isShared_2438_ = v_isSharedCheck_2450_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_v_2435_);
lean_inc(v_k_2434_);
lean_dec(v_r_2428_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2450_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2442_; 
v___x_2439_ = lean_unsigned_to_nat(3u);
v___x_2440_ = lean_unsigned_to_nat(1u);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 4, v_l_2390_);
lean_ctor_set(v___x_2437_, 3, v_l_2390_);
lean_ctor_set(v___x_2437_, 2, v_v_2430_);
lean_ctor_set(v___x_2437_, 1, v_k_2429_);
lean_ctor_set(v___x_2437_, 0, v___x_2440_);
v___x_2442_ = v___x_2437_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2440_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v_k_2429_);
lean_ctor_set(v_reuseFailAlloc_2449_, 2, v_v_2430_);
lean_ctor_set(v_reuseFailAlloc_2449_, 3, v_l_2390_);
lean_ctor_set(v_reuseFailAlloc_2449_, 4, v_l_2390_);
v___x_2442_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
lean_object* v___x_2444_; 
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 4, v_l_2390_);
lean_ctor_set(v___x_2432_, 2, v_v_2284_);
lean_ctor_set(v___x_2432_, 1, v_k_2283_);
lean_ctor_set(v___x_2432_, 0, v___x_2440_);
v___x_2444_ = v___x_2432_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2440_);
lean_ctor_set(v_reuseFailAlloc_2448_, 1, v_k_2283_);
lean_ctor_set(v_reuseFailAlloc_2448_, 2, v_v_2284_);
lean_ctor_set(v_reuseFailAlloc_2448_, 3, v_l_2390_);
lean_ctor_set(v_reuseFailAlloc_2448_, 4, v_l_2390_);
v___x_2444_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
lean_object* v___x_2446_; 
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 4, v___x_2444_);
lean_ctor_set(v___x_2288_, 3, v___x_2442_);
lean_ctor_set(v___x_2288_, 2, v_v_2435_);
lean_ctor_set(v___x_2288_, 1, v_k_2434_);
lean_ctor_set(v___x_2288_, 0, v___x_2439_);
v___x_2446_ = v___x_2288_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2447_, 1, v_k_2434_);
lean_ctor_set(v_reuseFailAlloc_2447_, 2, v_v_2435_);
lean_ctor_set(v_reuseFailAlloc_2447_, 3, v___x_2442_);
lean_ctor_set(v_reuseFailAlloc_2447_, 4, v___x_2444_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
}
}
else
{
lean_object* v___x_2458_; lean_object* v___x_2460_; 
v___x_2458_ = lean_unsigned_to_nat(2u);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 4, v_r_2428_);
lean_ctor_set(v___x_2288_, 3, v___x_2291_);
lean_ctor_set(v___x_2288_, 0, v___x_2458_);
v___x_2460_ = v___x_2288_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2458_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v_k_2283_);
lean_ctor_set(v_reuseFailAlloc_2461_, 2, v_v_2284_);
lean_ctor_set(v_reuseFailAlloc_2461_, 3, v___x_2291_);
lean_ctor_set(v_reuseFailAlloc_2461_, 4, v_r_2428_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
else
{
lean_object* v___x_2462_; lean_object* v___x_2464_; 
v___x_2462_ = lean_unsigned_to_nat(1u);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 4, v___x_2291_);
lean_ctor_set(v___x_2288_, 3, v___x_2291_);
lean_ctor_set(v___x_2288_, 0, v___x_2462_);
v___x_2464_ = v___x_2288_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v_k_2283_);
lean_ctor_set(v_reuseFailAlloc_2465_, 2, v_v_2284_);
lean_ctor_set(v_reuseFailAlloc_2465_, 3, v___x_2291_);
lean_ctor_set(v_reuseFailAlloc_2465_, 4, v___x_2291_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
case 1:
{
lean_object* v___x_2467_; 
lean_dec(v_v_2284_);
lean_dec(v_k_2283_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 2, v_v_2280_);
lean_ctor_set(v___x_2288_, 1, v_k_2279_);
v___x_2467_ = v___x_2288_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_size_2282_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_k_2279_);
lean_ctor_set(v_reuseFailAlloc_2468_, 2, v_v_2280_);
lean_ctor_set(v_reuseFailAlloc_2468_, 3, v_l_2285_);
lean_ctor_set(v_reuseFailAlloc_2468_, 4, v_r_2286_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
default: 
{
lean_object* v___x_2469_; 
lean_dec(v_size_2282_);
v___x_2469_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg(v_k_2279_, v_v_2280_, v_r_2286_);
if (lean_obj_tag(v_l_2285_) == 0)
{
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_size_2470_; lean_object* v_size_2471_; lean_object* v_k_2472_; lean_object* v_v_2473_; lean_object* v_l_2474_; lean_object* v_r_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; uint8_t v___x_2478_; 
v_size_2470_ = lean_ctor_get(v_l_2285_, 0);
v_size_2471_ = lean_ctor_get(v___x_2469_, 0);
v_k_2472_ = lean_ctor_get(v___x_2469_, 1);
v_v_2473_ = lean_ctor_get(v___x_2469_, 2);
v_l_2474_ = lean_ctor_get(v___x_2469_, 3);
lean_inc(v_l_2474_);
v_r_2475_ = lean_ctor_get(v___x_2469_, 4);
v___x_2476_ = lean_unsigned_to_nat(3u);
v___x_2477_ = lean_nat_mul(v___x_2476_, v_size_2470_);
v___x_2478_ = lean_nat_dec_lt(v___x_2477_, v_size_2471_);
lean_dec(v___x_2477_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2483_; 
lean_dec(v_l_2474_);
v___x_2479_ = lean_unsigned_to_nat(1u);
v___x_2480_ = lean_nat_add(v___x_2479_, v_size_2470_);
v___x_2481_ = lean_nat_add(v___x_2480_, v_size_2471_);
lean_dec(v___x_2480_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 4, v___x_2469_);
lean_ctor_set(v___x_2288_, 0, v___x_2481_);
v___x_2483_ = v___x_2288_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2484_, 1, v_k_2283_);
lean_ctor_set(v_reuseFailAlloc_2484_, 2, v_v_2284_);
lean_ctor_set(v_reuseFailAlloc_2484_, 3, v_l_2285_);
lean_ctor_set(v_reuseFailAlloc_2484_, 4, v___x_2469_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
else
{
lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2554_; 
lean_inc(v_r_2475_);
lean_inc(v_v_2473_);
lean_inc(v_k_2472_);
lean_inc(v_size_2471_);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2554_ == 0)
{
lean_object* v_unused_2555_; lean_object* v_unused_2556_; lean_object* v_unused_2557_; lean_object* v_unused_2558_; lean_object* v_unused_2559_; 
v_unused_2555_ = lean_ctor_get(v___x_2469_, 4);
lean_dec(v_unused_2555_);
v_unused_2556_ = lean_ctor_get(v___x_2469_, 3);
lean_dec(v_unused_2556_);
v_unused_2557_ = lean_ctor_get(v___x_2469_, 2);
lean_dec(v_unused_2557_);
v_unused_2558_ = lean_ctor_get(v___x_2469_, 1);
lean_dec(v_unused_2558_);
v_unused_2559_ = lean_ctor_get(v___x_2469_, 0);
lean_dec(v_unused_2559_);
v___x_2486_ = v___x_2469_;
v_isShared_2487_ = v_isSharedCheck_2554_;
goto v_resetjp_2485_;
}
else
{
lean_dec(v___x_2469_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2554_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
if (lean_obj_tag(v_l_2474_) == 0)
{
if (lean_obj_tag(v_r_2475_) == 0)
{
lean_object* v_size_2488_; lean_object* v_k_2489_; lean_object* v_v_2490_; lean_object* v_l_2491_; lean_object* v_r_2492_; lean_object* v_size_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; 
v_size_2488_ = lean_ctor_get(v_l_2474_, 0);
v_k_2489_ = lean_ctor_get(v_l_2474_, 1);
v_v_2490_ = lean_ctor_get(v_l_2474_, 2);
v_l_2491_ = lean_ctor_get(v_l_2474_, 3);
v_r_2492_ = lean_ctor_get(v_l_2474_, 4);
v_size_2493_ = lean_ctor_get(v_r_2475_, 0);
v___x_2494_ = lean_unsigned_to_nat(2u);
v___x_2495_ = lean_nat_mul(v___x_2494_, v_size_2493_);
v___x_2496_ = lean_nat_dec_lt(v_size_2488_, v___x_2495_);
lean_dec(v___x_2495_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2525_; 
lean_inc(v_r_2492_);
lean_inc(v_l_2491_);
lean_inc(v_v_2490_);
lean_inc(v_k_2489_);
v_isSharedCheck_2525_ = !lean_is_exclusive(v_l_2474_);
if (v_isSharedCheck_2525_ == 0)
{
lean_object* v_unused_2526_; lean_object* v_unused_2527_; lean_object* v_unused_2528_; lean_object* v_unused_2529_; lean_object* v_unused_2530_; 
v_unused_2526_ = lean_ctor_get(v_l_2474_, 4);
lean_dec(v_unused_2526_);
v_unused_2527_ = lean_ctor_get(v_l_2474_, 3);
lean_dec(v_unused_2527_);
v_unused_2528_ = lean_ctor_get(v_l_2474_, 2);
lean_dec(v_unused_2528_);
v_unused_2529_ = lean_ctor_get(v_l_2474_, 1);
lean_dec(v_unused_2529_);
v_unused_2530_ = lean_ctor_get(v_l_2474_, 0);
lean_dec(v_unused_2530_);
v___x_2498_ = v_l_2474_;
v_isShared_2499_ = v_isSharedCheck_2525_;
goto v_resetjp_2497_;
}
else
{
lean_dec(v_l_2474_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2525_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2515_; 
v___x_2500_ = lean_unsigned_to_nat(1u);
v___x_2501_ = lean_nat_add(v___x_2500_, v_size_2470_);
v___x_2502_ = lean_nat_add(v___x_2501_, v_size_2471_);
lean_dec(v_size_2471_);
if (lean_obj_tag(v_l_2491_) == 0)
{
lean_object* v_size_2523_; 
v_size_2523_ = lean_ctor_get(v_l_2491_, 0);
lean_inc(v_size_2523_);
v___y_2515_ = v_size_2523_;
goto v___jp_2514_;
}
else
{
lean_object* v___x_2524_; 
v___x_2524_ = lean_unsigned_to_nat(0u);
v___y_2515_ = v___x_2524_;
goto v___jp_2514_;
}
v___jp_2503_:
{
lean_object* v___x_2507_; lean_object* v___x_2509_; 
v___x_2507_ = lean_nat_add(v___y_2505_, v___y_2506_);
lean_dec(v___y_2506_);
lean_dec(v___y_2505_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 4, v_r_2475_);
lean_ctor_set(v___x_2498_, 3, v_r_2492_);
lean_ctor_set(v___x_2498_, 2, v_v_2473_);
lean_ctor_set(v___x_2498_, 1, v_k_2472_);
lean_ctor_set(v___x_2498_, 0, v___x_2507_);
v___x_2509_ = v___x_2498_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2507_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v_k_2472_);
lean_ctor_set(v_reuseFailAlloc_2513_, 2, v_v_2473_);
lean_ctor_set(v_reuseFailAlloc_2513_, 3, v_r_2492_);
lean_ctor_set(v_reuseFailAlloc_2513_, 4, v_r_2475_);
v___x_2509_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
lean_object* v___x_2511_; 
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 4, v___x_2509_);
lean_ctor_set(v___x_2486_, 3, v___y_2504_);
lean_ctor_set(v___x_2486_, 2, v_v_2490_);
lean_ctor_set(v___x_2486_, 1, v_k_2489_);
lean_ctor_set(v___x_2486_, 0, v___x_2502_);
v___x_2511_ = v___x_2486_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_k_2489_);
lean_ctor_set(v_reuseFailAlloc_2512_, 2, v_v_2490_);
lean_ctor_set(v_reuseFailAlloc_2512_, 3, v___y_2504_);
lean_ctor_set(v_reuseFailAlloc_2512_, 4, v___x_2509_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
v___jp_2514_:
{
lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2516_ = lean_nat_add(v___x_2501_, v___y_2515_);
lean_dec(v___y_2515_);
lean_dec(v___x_2501_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 4, v_l_2491_);
lean_ctor_set(v___x_2288_, 0, v___x_2516_);
v___x_2518_ = v___x_2288_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_k_2283_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v_v_2284_);
lean_ctor_set(v_reuseFailAlloc_2522_, 3, v_l_2285_);
lean_ctor_set(v_reuseFailAlloc_2522_, 4, v_l_2491_);
v___x_2518_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2519_; 
v___x_2519_ = lean_nat_add(v___x_2500_, v_size_2493_);
if (lean_obj_tag(v_r_2492_) == 0)
{
lean_object* v_size_2520_; 
v_size_2520_ = lean_ctor_get(v_r_2492_, 0);
lean_inc(v_size_2520_);
v___y_2504_ = v___x_2518_;
v___y_2505_ = v___x_2519_;
v___y_2506_ = v_size_2520_;
goto v___jp_2503_;
}
else
{
lean_object* v___x_2521_; 
v___x_2521_ = lean_unsigned_to_nat(0u);
v___y_2504_ = v___x_2518_;
v___y_2505_ = v___x_2519_;
v___y_2506_ = v___x_2521_;
goto v___jp_2503_;
}
}
}
}
}
else
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2536_; 
lean_del_object(v___x_2288_);
v___x_2531_ = lean_unsigned_to_nat(1u);
v___x_2532_ = lean_nat_add(v___x_2531_, v_size_2470_);
v___x_2533_ = lean_nat_add(v___x_2532_, v_size_2471_);
lean_dec(v_size_2471_);
v___x_2534_ = lean_nat_add(v___x_2532_, v_size_2488_);
lean_dec(v___x_2532_);
lean_inc_ref(v_l_2285_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 4, v_l_2474_);
lean_ctor_set(v___x_2486_, 3, v_l_2285_);
lean_ctor_set(v___x_2486_, 2, v_v_2284_);
lean_ctor_set(v___x_2486_, 1, v_k_2283_);
lean_ctor_set(v___x_2486_, 0, v___x_2534_);
v___x_2536_ = v___x_2486_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2534_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v_k_2283_);
lean_ctor_set(v_reuseFailAlloc_2549_, 2, v_v_2284_);
lean_ctor_set(v_reuseFailAlloc_2549_, 3, v_l_2285_);
lean_ctor_set(v_reuseFailAlloc_2549_, 4, v_l_2474_);
v___x_2536_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
v_isSharedCheck_2543_ = !lean_is_exclusive(v_l_2285_);
if (v_isSharedCheck_2543_ == 0)
{
lean_object* v_unused_2544_; lean_object* v_unused_2545_; lean_object* v_unused_2546_; lean_object* v_unused_2547_; lean_object* v_unused_2548_; 
v_unused_2544_ = lean_ctor_get(v_l_2285_, 4);
lean_dec(v_unused_2544_);
v_unused_2545_ = lean_ctor_get(v_l_2285_, 3);
lean_dec(v_unused_2545_);
v_unused_2546_ = lean_ctor_get(v_l_2285_, 2);
lean_dec(v_unused_2546_);
v_unused_2547_ = lean_ctor_get(v_l_2285_, 1);
lean_dec(v_unused_2547_);
v_unused_2548_ = lean_ctor_get(v_l_2285_, 0);
lean_dec(v_unused_2548_);
v___x_2538_ = v_l_2285_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_dec(v_l_2285_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 4, v_r_2475_);
lean_ctor_set(v___x_2538_, 3, v___x_2536_);
lean_ctor_set(v___x_2538_, 2, v_v_2473_);
lean_ctor_set(v___x_2538_, 1, v_k_2472_);
lean_ctor_set(v___x_2538_, 0, v___x_2533_);
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2533_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v_k_2472_);
lean_ctor_set(v_reuseFailAlloc_2542_, 2, v_v_2473_);
lean_ctor_set(v_reuseFailAlloc_2542_, 3, v___x_2536_);
lean_ctor_set(v_reuseFailAlloc_2542_, 4, v_r_2475_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
}
else
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
lean_dec_ref_known(v_l_2474_, 5);
lean_del_object(v___x_2486_);
lean_dec(v_v_2473_);
lean_dec(v_k_2472_);
lean_dec(v_size_2471_);
lean_dec_ref_known(v_l_2285_, 5);
lean_del_object(v___x_2288_);
lean_dec(v_v_2284_);
lean_dec(v_k_2283_);
v___x_2550_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__7);
v___x_2551_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4___redArg(v___x_2550_);
return v___x_2551_;
}
}
else
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
lean_del_object(v___x_2486_);
lean_dec(v_r_2475_);
lean_dec(v_v_2473_);
lean_dec(v_k_2472_);
lean_dec(v_size_2471_);
lean_dec_ref_known(v_l_2285_, 5);
lean_del_object(v___x_2288_);
lean_dec(v_v_2284_);
lean_dec(v_k_2283_);
v___x_2552_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__8);
v___x_2553_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4___redArg(v___x_2552_);
return v___x_2553_;
}
}
}
}
else
{
lean_object* v_size_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2564_; 
v_size_2560_ = lean_ctor_get(v_l_2285_, 0);
v___x_2561_ = lean_unsigned_to_nat(1u);
v___x_2562_ = lean_nat_add(v___x_2561_, v_size_2560_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 4, v___x_2469_);
lean_ctor_set(v___x_2288_, 0, v___x_2562_);
v___x_2564_ = v___x_2288_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2562_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_k_2283_);
lean_ctor_set(v_reuseFailAlloc_2565_, 2, v_v_2284_);
lean_ctor_set(v_reuseFailAlloc_2565_, 3, v_l_2285_);
lean_ctor_set(v_reuseFailAlloc_2565_, 4, v___x_2469_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
else
{
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_l_2566_; 
v_l_2566_ = lean_ctor_get(v___x_2469_, 3);
lean_inc(v_l_2566_);
if (lean_obj_tag(v_l_2566_) == 0)
{
lean_object* v_r_2567_; 
v_r_2567_ = lean_ctor_get(v___x_2469_, 4);
lean_inc(v_r_2567_);
if (lean_obj_tag(v_r_2567_) == 0)
{
lean_object* v_size_2568_; lean_object* v_k_2569_; lean_object* v_v_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2584_; 
v_size_2568_ = lean_ctor_get(v___x_2469_, 0);
v_k_2569_ = lean_ctor_get(v___x_2469_, 1);
v_v_2570_ = lean_ctor_get(v___x_2469_, 2);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2584_ == 0)
{
lean_object* v_unused_2585_; lean_object* v_unused_2586_; 
v_unused_2585_ = lean_ctor_get(v___x_2469_, 4);
lean_dec(v_unused_2585_);
v_unused_2586_ = lean_ctor_get(v___x_2469_, 3);
lean_dec(v_unused_2586_);
v___x_2572_ = v___x_2469_;
v_isShared_2573_ = v_isSharedCheck_2584_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_v_2570_);
lean_inc(v_k_2569_);
lean_inc(v_size_2568_);
lean_dec(v___x_2469_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2584_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v_size_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2579_; 
v_size_2574_ = lean_ctor_get(v_l_2566_, 0);
v___x_2575_ = lean_unsigned_to_nat(1u);
v___x_2576_ = lean_nat_add(v___x_2575_, v_size_2568_);
lean_dec(v_size_2568_);
v___x_2577_ = lean_nat_add(v___x_2575_, v_size_2574_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 4, v_l_2566_);
lean_ctor_set(v___x_2572_, 3, v_l_2285_);
lean_ctor_set(v___x_2572_, 2, v_v_2284_);
lean_ctor_set(v___x_2572_, 1, v_k_2283_);
lean_ctor_set(v___x_2572_, 0, v___x_2577_);
v___x_2579_ = v___x_2572_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2577_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_k_2283_);
lean_ctor_set(v_reuseFailAlloc_2583_, 2, v_v_2284_);
lean_ctor_set(v_reuseFailAlloc_2583_, 3, v_l_2285_);
lean_ctor_set(v_reuseFailAlloc_2583_, 4, v_l_2566_);
v___x_2579_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2581_; 
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 4, v_r_2567_);
lean_ctor_set(v___x_2288_, 3, v___x_2579_);
lean_ctor_set(v___x_2288_, 2, v_v_2570_);
lean_ctor_set(v___x_2288_, 1, v_k_2569_);
lean_ctor_set(v___x_2288_, 0, v___x_2576_);
v___x_2581_ = v___x_2288_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2576_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v_k_2569_);
lean_ctor_set(v_reuseFailAlloc_2582_, 2, v_v_2570_);
lean_ctor_set(v_reuseFailAlloc_2582_, 3, v___x_2579_);
lean_ctor_set(v_reuseFailAlloc_2582_, 4, v_r_2567_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
else
{
lean_object* v_k_2587_; lean_object* v_v_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2612_; 
v_k_2587_ = lean_ctor_get(v___x_2469_, 1);
v_v_2588_ = lean_ctor_get(v___x_2469_, 2);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2612_ == 0)
{
lean_object* v_unused_2613_; lean_object* v_unused_2614_; lean_object* v_unused_2615_; 
v_unused_2613_ = lean_ctor_get(v___x_2469_, 4);
lean_dec(v_unused_2613_);
v_unused_2614_ = lean_ctor_get(v___x_2469_, 3);
lean_dec(v_unused_2614_);
v_unused_2615_ = lean_ctor_get(v___x_2469_, 0);
lean_dec(v_unused_2615_);
v___x_2590_ = v___x_2469_;
v_isShared_2591_ = v_isSharedCheck_2612_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_v_2588_);
lean_inc(v_k_2587_);
lean_dec(v___x_2469_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2612_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v_k_2592_; lean_object* v_v_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2608_; 
v_k_2592_ = lean_ctor_get(v_l_2566_, 1);
v_v_2593_ = lean_ctor_get(v_l_2566_, 2);
v_isSharedCheck_2608_ = !lean_is_exclusive(v_l_2566_);
if (v_isSharedCheck_2608_ == 0)
{
lean_object* v_unused_2609_; lean_object* v_unused_2610_; lean_object* v_unused_2611_; 
v_unused_2609_ = lean_ctor_get(v_l_2566_, 4);
lean_dec(v_unused_2609_);
v_unused_2610_ = lean_ctor_get(v_l_2566_, 3);
lean_dec(v_unused_2610_);
v_unused_2611_ = lean_ctor_get(v_l_2566_, 0);
lean_dec(v_unused_2611_);
v___x_2595_ = v_l_2566_;
v_isShared_2596_ = v_isSharedCheck_2608_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_v_2593_);
lean_inc(v_k_2592_);
lean_dec(v_l_2566_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2608_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2600_; 
v___x_2597_ = lean_unsigned_to_nat(3u);
v___x_2598_ = lean_unsigned_to_nat(1u);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 4, v_r_2567_);
lean_ctor_set(v___x_2595_, 3, v_r_2567_);
lean_ctor_set(v___x_2595_, 2, v_v_2284_);
lean_ctor_set(v___x_2595_, 1, v_k_2283_);
lean_ctor_set(v___x_2595_, 0, v___x_2598_);
v___x_2600_ = v___x_2595_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2598_);
lean_ctor_set(v_reuseFailAlloc_2607_, 1, v_k_2283_);
lean_ctor_set(v_reuseFailAlloc_2607_, 2, v_v_2284_);
lean_ctor_set(v_reuseFailAlloc_2607_, 3, v_r_2567_);
lean_ctor_set(v_reuseFailAlloc_2607_, 4, v_r_2567_);
v___x_2600_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v___x_2602_; 
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 3, v_r_2567_);
lean_ctor_set(v___x_2590_, 0, v___x_2598_);
v___x_2602_ = v___x_2590_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2598_);
lean_ctor_set(v_reuseFailAlloc_2606_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_2606_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_2606_, 3, v_r_2567_);
lean_ctor_set(v_reuseFailAlloc_2606_, 4, v_r_2567_);
v___x_2602_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
lean_object* v___x_2604_; 
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 4, v___x_2602_);
lean_ctor_set(v___x_2288_, 3, v___x_2600_);
lean_ctor_set(v___x_2288_, 2, v_v_2593_);
lean_ctor_set(v___x_2288_, 1, v_k_2592_);
lean_ctor_set(v___x_2288_, 0, v___x_2597_);
v___x_2604_ = v___x_2288_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2605_, 1, v_k_2592_);
lean_ctor_set(v_reuseFailAlloc_2605_, 2, v_v_2593_);
lean_ctor_set(v_reuseFailAlloc_2605_, 3, v___x_2600_);
lean_ctor_set(v_reuseFailAlloc_2605_, 4, v___x_2602_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_2616_; 
v_r_2616_ = lean_ctor_get(v___x_2469_, 4);
lean_inc(v_r_2616_);
if (lean_obj_tag(v_r_2616_) == 0)
{
lean_object* v_k_2617_; lean_object* v_v_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2630_; 
v_k_2617_ = lean_ctor_get(v___x_2469_, 1);
v_v_2618_ = lean_ctor_get(v___x_2469_, 2);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2630_ == 0)
{
lean_object* v_unused_2631_; lean_object* v_unused_2632_; lean_object* v_unused_2633_; 
v_unused_2631_ = lean_ctor_get(v___x_2469_, 4);
lean_dec(v_unused_2631_);
v_unused_2632_ = lean_ctor_get(v___x_2469_, 3);
lean_dec(v_unused_2632_);
v_unused_2633_ = lean_ctor_get(v___x_2469_, 0);
lean_dec(v_unused_2633_);
v___x_2620_ = v___x_2469_;
v_isShared_2621_ = v_isSharedCheck_2630_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_v_2618_);
lean_inc(v_k_2617_);
lean_dec(v___x_2469_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2630_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2625_; 
v___x_2622_ = lean_unsigned_to_nat(3u);
v___x_2623_ = lean_unsigned_to_nat(1u);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 4, v_l_2566_);
lean_ctor_set(v___x_2620_, 2, v_v_2284_);
lean_ctor_set(v___x_2620_, 1, v_k_2283_);
lean_ctor_set(v___x_2620_, 0, v___x_2623_);
v___x_2625_ = v___x_2620_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2623_);
lean_ctor_set(v_reuseFailAlloc_2629_, 1, v_k_2283_);
lean_ctor_set(v_reuseFailAlloc_2629_, 2, v_v_2284_);
lean_ctor_set(v_reuseFailAlloc_2629_, 3, v_l_2566_);
lean_ctor_set(v_reuseFailAlloc_2629_, 4, v_l_2566_);
v___x_2625_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
lean_object* v___x_2627_; 
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 4, v_r_2616_);
lean_ctor_set(v___x_2288_, 3, v___x_2625_);
lean_ctor_set(v___x_2288_, 2, v_v_2618_);
lean_ctor_set(v___x_2288_, 1, v_k_2617_);
lean_ctor_set(v___x_2288_, 0, v___x_2622_);
v___x_2627_ = v___x_2288_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2622_);
lean_ctor_set(v_reuseFailAlloc_2628_, 1, v_k_2617_);
lean_ctor_set(v_reuseFailAlloc_2628_, 2, v_v_2618_);
lean_ctor_set(v_reuseFailAlloc_2628_, 3, v___x_2625_);
lean_ctor_set(v_reuseFailAlloc_2628_, 4, v_r_2616_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
else
{
lean_object* v___x_2634_; lean_object* v___x_2636_; 
v___x_2634_ = lean_unsigned_to_nat(2u);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 4, v___x_2469_);
lean_ctor_set(v___x_2288_, 3, v_r_2616_);
lean_ctor_set(v___x_2288_, 0, v___x_2634_);
v___x_2636_ = v___x_2288_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v_k_2283_);
lean_ctor_set(v_reuseFailAlloc_2637_, 2, v_v_2284_);
lean_ctor_set(v_reuseFailAlloc_2637_, 3, v_r_2616_);
lean_ctor_set(v_reuseFailAlloc_2637_, 4, v___x_2469_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
else
{
lean_object* v___x_2638_; lean_object* v___x_2640_; 
v___x_2638_ = lean_unsigned_to_nat(1u);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 4, v___x_2469_);
lean_ctor_set(v___x_2288_, 3, v___x_2469_);
lean_ctor_set(v___x_2288_, 0, v___x_2638_);
v___x_2640_ = v___x_2288_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2638_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v_k_2283_);
lean_ctor_set(v_reuseFailAlloc_2641_, 2, v_v_2284_);
lean_ctor_set(v_reuseFailAlloc_2641_, 3, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2641_, 4, v___x_2469_);
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
}
}
}
else
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = lean_unsigned_to_nat(1u);
v___x_2644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2643_);
lean_ctor_set(v___x_2644_, 1, v_k_2279_);
lean_ctor_set(v___x_2644_, 2, v_v_2280_);
lean_ctor_set(v___x_2644_, 3, v_t_2281_);
lean_ctor_set(v___x_2644_, 4, v_t_2281_);
return v___x_2644_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__3_spec__6(lean_object* v_init_2645_, lean_object* v_x_2646_){
_start:
{
if (lean_obj_tag(v_x_2646_) == 0)
{
lean_object* v_k_2647_; lean_object* v_v_2648_; lean_object* v_l_2649_; lean_object* v_r_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
v_k_2647_ = lean_ctor_get(v_x_2646_, 1);
lean_inc(v_k_2647_);
v_v_2648_ = lean_ctor_get(v_x_2646_, 2);
lean_inc(v_v_2648_);
v_l_2649_ = lean_ctor_get(v_x_2646_, 3);
lean_inc(v_l_2649_);
v_r_2650_ = lean_ctor_get(v_x_2646_, 4);
lean_inc(v_r_2650_);
lean_dec_ref_known(v_x_2646_, 5);
v___x_2651_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__3_spec__6(v_init_2645_, v_l_2649_);
v___x_2652_ = 1;
v___x_2653_ = l_Lean_Name_toString(v_k_2647_, v___x_2652_);
v___x_2654_ = l_Lean_Array_toJson___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1(v_v_2648_);
v___x_2655_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg(v___x_2653_, v___x_2654_, v___x_2651_);
v_init_2645_ = v___x_2655_;
v_x_2646_ = v_r_2650_;
goto _start;
}
else
{
return v_init_2645_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1(lean_object* v_m_2657_){
_start:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2658_ = lean_box(1);
v___x_2659_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__3_spec__6(v___x_2658_, v_m_2657_);
v___x_2660_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2659_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonModuleSetup_toJson_spec__0(lean_object* v_k_2661_, lean_object* v_x_2662_){
_start:
{
if (lean_obj_tag(v_x_2662_) == 0)
{
lean_object* v___x_2663_; 
lean_dec_ref(v_k_2661_);
v___x_2663_ = lean_box(0);
return v___x_2663_;
}
else
{
lean_object* v_val_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v_val_2664_ = lean_ctor_get(v_x_2662_, 0);
lean_inc(v_val_2664_);
lean_dec_ref_known(v_x_2662_, 1);
v___x_2665_ = l_Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0(v_val_2664_);
v___x_2666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2666_, 0, v_k_2661_);
lean_ctor_set(v___x_2666_, 1, v___x_2665_);
v___x_2667_ = lean_box(0);
v___x_2668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2666_);
lean_ctor_set(v___x_2668_, 1, v___x_2667_);
return v___x_2668_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__9_spec__13(lean_object* v_init_2669_, lean_object* v_x_2670_){
_start:
{
if (lean_obj_tag(v_x_2670_) == 0)
{
lean_object* v_k_2671_; lean_object* v_v_2672_; lean_object* v_l_2673_; lean_object* v_r_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; lean_object* v___x_2677_; lean_object* v___y_2679_; 
v_k_2671_ = lean_ctor_get(v_x_2670_, 1);
lean_inc(v_k_2671_);
v_v_2672_ = lean_ctor_get(v_x_2670_, 2);
lean_inc(v_v_2672_);
v_l_2673_ = lean_ctor_get(v_x_2670_, 3);
lean_inc(v_l_2673_);
v_r_2674_ = lean_ctor_get(v_x_2670_, 4);
lean_inc(v_r_2674_);
lean_dec_ref_known(v_x_2670_, 5);
v___x_2675_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__9_spec__13(v_init_2669_, v_l_2673_);
v___x_2676_ = 1;
v___x_2677_ = l_Lean_Name_toString(v_k_2671_, v___x_2676_);
switch(lean_obj_tag(v_v_2672_))
{
case 0:
{
lean_object* v_s_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
v_s_2682_ = lean_ctor_get(v_v_2672_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v_v_2672_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v_v_2672_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_s_2682_);
lean_dec(v_v_2672_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
lean_ctor_set_tag(v___x_2684_, 3);
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_s_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
v___y_2679_ = v___x_2687_;
goto v___jp_2678_;
}
}
}
case 1:
{
uint8_t v_b_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
v_b_2690_ = lean_ctor_get_uint8(v_v_2672_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v_v_2672_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v_v_2672_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_dec(v_v_2672_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2696_, 0, v_b_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
v___y_2679_ = v___x_2695_;
goto v___jp_2678_;
}
}
}
default: 
{
lean_object* v_n_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2706_; 
v_n_2698_ = lean_ctor_get(v_v_2672_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v_v_2672_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2700_ = v_v_2672_;
v_isShared_2701_ = v_isSharedCheck_2706_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_n_2698_);
lean_dec(v_v_2672_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2706_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2702_; lean_object* v___x_2704_; 
v___x_2702_ = l_Lean_JsonNumber_fromNat(v_n_2698_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v___x_2702_);
v___x_2704_ = v___x_2700_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2702_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
v___y_2679_ = v___x_2704_;
goto v___jp_2678_;
}
}
}
}
v___jp_2678_:
{
lean_object* v___x_2680_; 
v___x_2680_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg(v___x_2677_, v___y_2679_, v___x_2675_);
v_init_2669_ = v___x_2680_;
v_x_2670_ = v_r_2674_;
goto _start;
}
}
else
{
return v_init_2669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4(lean_object* v_m_2707_){
_start:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2708_ = lean_box(1);
v___x_2709_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__9_spec__13(v___x_2708_, v_m_2707_);
v___x_2710_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__7(size_t v_sz_2711_, size_t v_i_2712_, lean_object* v_bs_2713_){
_start:
{
uint8_t v___x_2714_; 
v___x_2714_ = lean_usize_dec_lt(v_i_2712_, v_sz_2711_);
if (v___x_2714_ == 0)
{
return v_bs_2713_;
}
else
{
lean_object* v_v_2715_; lean_object* v___x_2716_; lean_object* v_bs_x27_2717_; lean_object* v___x_2718_; size_t v___x_2719_; size_t v___x_2720_; lean_object* v___x_2721_; 
v_v_2715_ = lean_array_uget(v_bs_2713_, v_i_2712_);
v___x_2716_ = lean_unsigned_to_nat(0u);
v_bs_x27_2717_ = lean_array_uset(v_bs_2713_, v_i_2712_, v___x_2716_);
v___x_2718_ = l_Lean_instToJsonPlugin_toJson(v_v_2715_);
v___x_2719_ = ((size_t)1ULL);
v___x_2720_ = lean_usize_add(v_i_2712_, v___x_2719_);
v___x_2721_ = lean_array_uset(v_bs_x27_2717_, v_i_2712_, v___x_2718_);
v_i_2712_ = v___x_2720_;
v_bs_2713_ = v___x_2721_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__7___boxed(lean_object* v_sz_2723_, lean_object* v_i_2724_, lean_object* v_bs_2725_){
_start:
{
size_t v_sz_boxed_2726_; size_t v_i_boxed_2727_; lean_object* v_res_2728_; 
v_sz_boxed_2726_ = lean_unbox_usize(v_sz_2723_);
lean_dec(v_sz_2723_);
v_i_boxed_2727_ = lean_unbox_usize(v_i_2724_);
lean_dec(v_i_2724_);
v_res_2728_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__7(v_sz_boxed_2726_, v_i_boxed_2727_, v_bs_2725_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3(lean_object* v_a_2729_){
_start:
{
size_t v_sz_2730_; size_t v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v_sz_2730_ = lean_array_size(v_a_2729_);
v___x_2731_ = ((size_t)0ULL);
v___x_2732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__7(v_sz_2730_, v___x_2731_, v_a_2729_);
v___x_2733_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonModuleSetup_toJson(lean_object* v_x_2735_){
_start:
{
lean_object* v_name_2736_; lean_object* v_package_x3f_2737_; uint8_t v_isModule_2738_; lean_object* v_imports_x3f_2739_; lean_object* v_importArts_2740_; lean_object* v_dynlibs_2741_; lean_object* v_plugins_2742_; lean_object* v_options_2743_; lean_object* v___x_2744_; uint8_t v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
v_name_2736_ = lean_ctor_get(v_x_2735_, 0);
lean_inc(v_name_2736_);
v_package_x3f_2737_ = lean_ctor_get(v_x_2735_, 1);
lean_inc(v_package_x3f_2737_);
v_isModule_2738_ = lean_ctor_get_uint8(v_x_2735_, sizeof(void*)*7);
v_imports_x3f_2739_ = lean_ctor_get(v_x_2735_, 2);
lean_inc(v_imports_x3f_2739_);
v_importArts_2740_ = lean_ctor_get(v_x_2735_, 3);
lean_inc(v_importArts_2740_);
v_dynlibs_2741_ = lean_ctor_get(v_x_2735_, 4);
lean_inc_ref(v_dynlibs_2741_);
v_plugins_2742_ = lean_ctor_get(v_x_2735_, 5);
lean_inc_ref(v_plugins_2742_);
v_options_2743_ = lean_ctor_get(v_x_2735_, 6);
lean_inc(v_options_2743_);
lean_dec_ref(v_x_2735_);
v___x_2744_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__0));
v___x_2745_ = 1;
v___x_2746_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2736_, v___x_2745_);
v___x_2747_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2746_);
v___x_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2744_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___x_2749_ = lean_box(0);
v___x_2750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2748_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = ((lean_object*)(l_Lean_instToJsonModuleSetup_toJson___closed__0));
v___x_2752_ = l_Lean_Json_opt___at___00Lean_instToJsonPlugin_toJson_spec__0(v___x_2751_, v_package_x3f_2737_);
v___x_2753_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__5));
v___x_2754_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2754_, 0, v_isModule_2738_);
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2753_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___x_2756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
lean_ctor_set(v___x_2756_, 1, v___x_2749_);
v___x_2757_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__0));
v___x_2758_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleSetup_toJson_spec__0(v___x_2757_, v_imports_x3f_2739_);
v___x_2759_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__8));
v___x_2760_ = l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1(v_importArts_2740_);
v___x_2761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2759_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
v___x_2762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2761_);
lean_ctor_set(v___x_2762_, 1, v___x_2749_);
v___x_2763_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__12));
v___x_2764_ = l_Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2(v_dynlibs_2741_);
v___x_2765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2763_);
lean_ctor_set(v___x_2765_, 1, v___x_2764_);
v___x_2766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
lean_ctor_set(v___x_2766_, 1, v___x_2749_);
v___x_2767_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__14));
v___x_2768_ = l_Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3(v_plugins_2742_);
v___x_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2767_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
v___x_2770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
lean_ctor_set(v___x_2770_, 1, v___x_2749_);
v___x_2771_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__16));
v___x_2772_ = l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4(v_options_2743_);
v___x_2773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2771_);
lean_ctor_set(v___x_2773_, 1, v___x_2772_);
v___x_2774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
lean_ctor_set(v___x_2774_, 1, v___x_2749_);
v___x_2775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
lean_ctor_set(v___x_2775_, 1, v___x_2749_);
v___x_2776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2770_);
lean_ctor_set(v___x_2776_, 1, v___x_2775_);
v___x_2777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2766_);
lean_ctor_set(v___x_2777_, 1, v___x_2776_);
v___x_2778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2762_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
v___x_2779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2758_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
v___x_2780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2756_);
lean_ctor_set(v___x_2780_, 1, v___x_2779_);
v___x_2781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2752_);
lean_ctor_set(v___x_2781_, 1, v___x_2780_);
v___x_2782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2750_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
v___x_2783_ = ((lean_object*)(l_Lean_instToJsonImport_toJson___closed__0));
v___x_2784_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(v___x_2782_, v___x_2783_);
v___x_2785_ = l_Lean_Json_mkObj(v___x_2784_);
lean_dec(v___x_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2786_, lean_object* v_msg_2787_){
_start:
{
lean_object* v___x_2788_; 
v___x_2788_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4___redArg(v_msg_2787_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2(lean_object* v_00_u03b2_2789_, lean_object* v_k_2790_, lean_object* v_v_2791_, lean_object* v_t_2792_){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg(v_k_2790_, v_v_2791_, v_t_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__3(lean_object* v_init_2794_, lean_object* v_t_2795_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__3_spec__6(v_init_2794_, v_t_2795_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__9(lean_object* v_init_2797_, lean_object* v_t_2798_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__9_spec__13(v_init_2797_, v_t_2798_);
return v___x_2799_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3(void){
_start:
{
lean_object* v_natZero_2806_; lean_object* v_intZero_2807_; 
v_natZero_2806_ = lean_unsigned_to_nat(0u);
v_intZero_2807_ = lean_nat_to_int(v_natZero_2806_);
return v_intZero_2807_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13(lean_object* v_init_2809_, lean_object* v_x_2810_){
_start:
{
if (lean_obj_tag(v_x_2810_) == 0)
{
lean_object* v_k_2815_; lean_object* v_v_2816_; lean_object* v_l_2817_; lean_object* v_r_2818_; lean_object* v___x_2819_; 
v_k_2815_ = lean_ctor_get(v_x_2810_, 1);
lean_inc(v_k_2815_);
v_v_2816_ = lean_ctor_get(v_x_2810_, 2);
lean_inc(v_v_2816_);
v_l_2817_ = lean_ctor_get(v_x_2810_, 3);
lean_inc(v_l_2817_);
v_r_2818_ = lean_ctor_get(v_x_2810_, 4);
lean_inc(v_r_2818_);
lean_dec_ref_known(v_x_2810_, 5);
v___x_2819_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13(v_init_2809_, v_l_2817_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_dec(v_r_2818_);
lean_dec(v_v_2816_);
lean_dec(v_k_2815_);
return v___x_2819_;
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2906_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2822_ = v___x_2819_;
v_isShared_2823_ = v_isSharedCheck_2906_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2819_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2906_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v_a_2825_; lean_object* v___x_2829_; uint8_t v___x_2830_; 
v___x_2829_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__2));
v___x_2830_ = lean_string_dec_eq(v_k_2815_, v___x_2829_);
if (v___x_2830_ == 0)
{
lean_object* v_n_2831_; lean_object* v_a_2833_; uint8_t v___x_2836_; 
lean_inc(v_k_2815_);
v_n_2831_ = l_String_toName(v_k_2815_);
v___x_2836_ = l_Lean_Name_isAnonymous(v_n_2831_);
if (v___x_2836_ == 0)
{
lean_del_object(v___x_2822_);
lean_dec(v_k_2815_);
switch(lean_obj_tag(v_v_2816_))
{
case 3:
{
lean_object* v_s_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
v_s_2837_ = lean_ctor_get(v_v_2816_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v_v_2816_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v_v_2816_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_s_2837_);
lean_dec(v_v_2816_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
lean_ctor_set_tag(v___x_2839_, 0);
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_s_2837_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
v_a_2833_ = v___x_2842_;
goto v___jp_2832_;
}
}
}
case 1:
{
uint8_t v_b_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
v_b_2845_ = lean_ctor_get_uint8(v_v_2816_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v_v_2816_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v_v_2816_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_dec(v_v_2816_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2851_, 0, v_b_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
v_a_2833_ = v___x_2850_;
goto v___jp_2832_;
}
}
}
case 2:
{
lean_object* v_n_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2867_; 
v_n_2853_ = lean_ctor_get(v_v_2816_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v_v_2816_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2855_ = v_v_2816_;
v_isShared_2856_ = v_isSharedCheck_2867_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_n_2853_);
lean_dec(v_v_2816_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2867_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v_mantissa_2857_; lean_object* v_exponent_2858_; lean_object* v_natZero_2859_; lean_object* v_intZero_2860_; uint8_t v_isNeg_2861_; 
v_mantissa_2857_ = lean_ctor_get(v_n_2853_, 0);
lean_inc(v_mantissa_2857_);
v_exponent_2858_ = lean_ctor_get(v_n_2853_, 1);
lean_inc(v_exponent_2858_);
lean_dec_ref(v_n_2853_);
v_natZero_2859_ = lean_unsigned_to_nat(0u);
v_intZero_2860_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3);
v_isNeg_2861_ = lean_int_dec_lt(v_mantissa_2857_, v_intZero_2860_);
if (v_isNeg_2861_ == 0)
{
uint8_t v___x_2862_; 
v___x_2862_ = lean_nat_dec_eq(v_exponent_2858_, v_natZero_2859_);
lean_dec(v_exponent_2858_);
if (v___x_2862_ == 0)
{
lean_dec(v_mantissa_2857_);
lean_del_object(v___x_2855_);
lean_dec(v_n_2831_);
lean_dec(v_a_2820_);
lean_dec(v_r_2818_);
goto v___jp_2813_;
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; 
v_a_2863_ = lean_nat_abs(v_mantissa_2857_);
lean_dec(v_mantissa_2857_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v_a_2863_);
v___x_2865_ = v___x_2855_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2863_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
v_a_2833_ = v___x_2865_;
goto v___jp_2832_;
}
}
}
else
{
lean_dec(v_exponent_2858_);
lean_dec(v_mantissa_2857_);
lean_del_object(v___x_2855_);
lean_dec(v_n_2831_);
lean_dec(v_a_2820_);
lean_dec(v_r_2818_);
goto v___jp_2813_;
}
}
}
default: 
{
lean_dec(v_n_2831_);
lean_dec(v_a_2820_);
lean_dec(v_r_2818_);
lean_dec(v_v_2816_);
goto v___jp_2813_;
}
}
}
else
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2873_; 
lean_dec(v_n_2831_);
lean_dec(v_a_2820_);
lean_dec(v_r_2818_);
lean_dec(v_v_2816_);
v___x_2868_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__4));
v___x_2869_ = lean_string_append(v___x_2868_, v_k_2815_);
lean_dec(v_k_2815_);
v___x_2870_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_2871_ = lean_string_append(v___x_2869_, v___x_2870_);
if (v_isShared_2823_ == 0)
{
lean_ctor_set_tag(v___x_2822_, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2871_);
v___x_2873_ = v___x_2822_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2871_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
v___jp_2832_:
{
lean_object* v___x_2834_; 
v___x_2834_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_2831_, v_a_2833_, v_a_2820_);
v_init_2809_ = v___x_2834_;
v_x_2810_ = v_r_2818_;
goto _start;
}
}
else
{
lean_del_object(v___x_2822_);
lean_dec(v_k_2815_);
switch(lean_obj_tag(v_v_2816_))
{
case 3:
{
lean_object* v_s_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
v_s_2875_ = lean_ctor_get(v_v_2816_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v_v_2816_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v_v_2816_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_s_2875_);
lean_dec(v_v_2816_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
lean_ctor_set_tag(v___x_2877_, 0);
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_s_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
v_a_2825_ = v___x_2880_;
goto v___jp_2824_;
}
}
}
case 1:
{
uint8_t v_b_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
v_b_2883_ = lean_ctor_get_uint8(v_v_2816_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v_v_2816_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v_v_2816_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_dec(v_v_2816_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2889_, 0, v_b_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
v_a_2825_ = v___x_2888_;
goto v___jp_2824_;
}
}
}
case 2:
{
lean_object* v_n_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2905_; 
v_n_2891_ = lean_ctor_get(v_v_2816_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v_v_2816_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2893_ = v_v_2816_;
v_isShared_2894_ = v_isSharedCheck_2905_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_n_2891_);
lean_dec(v_v_2816_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2905_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v_mantissa_2895_; lean_object* v_exponent_2896_; lean_object* v_natZero_2897_; lean_object* v_intZero_2898_; uint8_t v_isNeg_2899_; 
v_mantissa_2895_ = lean_ctor_get(v_n_2891_, 0);
lean_inc(v_mantissa_2895_);
v_exponent_2896_ = lean_ctor_get(v_n_2891_, 1);
lean_inc(v_exponent_2896_);
lean_dec_ref(v_n_2891_);
v_natZero_2897_ = lean_unsigned_to_nat(0u);
v_intZero_2898_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3);
v_isNeg_2899_ = lean_int_dec_lt(v_mantissa_2895_, v_intZero_2898_);
if (v_isNeg_2899_ == 0)
{
uint8_t v___x_2900_; 
v___x_2900_ = lean_nat_dec_eq(v_exponent_2896_, v_natZero_2897_);
lean_dec(v_exponent_2896_);
if (v___x_2900_ == 0)
{
lean_dec(v_mantissa_2895_);
lean_del_object(v___x_2893_);
lean_dec(v_a_2820_);
lean_dec(v_r_2818_);
goto v___jp_2811_;
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; 
v_a_2901_ = lean_nat_abs(v_mantissa_2895_);
lean_dec(v_mantissa_2895_);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 0, v_a_2901_);
v___x_2903_ = v___x_2893_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2901_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
v_a_2825_ = v___x_2903_;
goto v___jp_2824_;
}
}
}
else
{
lean_dec(v_exponent_2896_);
lean_dec(v_mantissa_2895_);
lean_del_object(v___x_2893_);
lean_dec(v_a_2820_);
lean_dec(v_r_2818_);
goto v___jp_2811_;
}
}
}
default: 
{
lean_dec(v_a_2820_);
lean_dec(v_r_2818_);
lean_dec(v_v_2816_);
goto v___jp_2811_;
}
}
}
v___jp_2824_:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = lean_box(0);
v___x_2827_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2826_, v_a_2825_, v_a_2820_);
v_init_2809_ = v___x_2827_;
v_x_2810_ = v_r_2818_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_2907_; 
v___x_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2907_, 0, v_init_2809_);
return v___x_2907_;
}
v___jp_2811_:
{
lean_object* v___x_2812_; 
v___x_2812_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__1));
return v___x_2812_;
}
v___jp_2813_:
{
lean_object* v___x_2814_; 
v___x_2814_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__1));
return v___x_2814_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8(lean_object* v_x_2909_){
_start:
{
if (lean_obj_tag(v_x_2909_) == 5)
{
lean_object* v_kvPairs_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v_kvPairs_2910_ = lean_ctor_get(v_x_2909_, 0);
lean_inc(v_kvPairs_2910_);
lean_dec_ref_known(v_x_2909_, 1);
v___x_2911_ = lean_box(1);
v___x_2912_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13(v___x_2911_, v_kvPairs_2910_);
return v___x_2912_;
}
else
{
lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2913_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8___closed__0));
v___x_2914_ = lean_unsigned_to_nat(80u);
v___x_2915_ = l_Lean_Json_pretty(v_x_2909_, v___x_2914_);
v___x_2916_ = lean_string_append(v___x_2913_, v___x_2915_);
lean_dec_ref(v___x_2915_);
v___x_2917_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_2918_ = lean_string_append(v___x_2916_, v___x_2917_);
v___x_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
return v___x_2919_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4(lean_object* v_j_2920_, lean_object* v_k_2921_){
_start:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2922_ = l_Lean_Json_getObjValD(v_j_2920_, v_k_2921_);
v___x_2923_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8(v___x_2922_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2923_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2923_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
else
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
v_a_2932_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2934_ = v___x_2923_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2923_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2932_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4___boxed(lean_object* v_j_2940_, lean_object* v_k_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4(v_j_2940_, v_k_2941_);
lean_dec_ref(v_k_2941_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__10(size_t v_sz_2943_, size_t v_i_2944_, lean_object* v_bs_2945_){
_start:
{
uint8_t v___x_2946_; 
v___x_2946_ = lean_usize_dec_lt(v_i_2944_, v_sz_2943_);
if (v___x_2946_ == 0)
{
lean_object* v___x_2947_; 
v___x_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2947_, 0, v_bs_2945_);
return v___x_2947_;
}
else
{
lean_object* v_v_2948_; lean_object* v___x_2949_; 
v_v_2948_ = lean_array_uget_borrowed(v_bs_2945_, v_i_2944_);
lean_inc(v_v_2948_);
v___x_2949_ = l_Lean_Plugin_fromJson_x3f(v_v_2948_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
lean_dec_ref(v_bs_2945_);
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2949_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2949_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
else
{
lean_object* v_a_2958_; lean_object* v___x_2959_; lean_object* v_bs_x27_2960_; size_t v___x_2961_; size_t v___x_2962_; lean_object* v___x_2963_; 
v_a_2958_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2958_);
lean_dec_ref_known(v___x_2949_, 1);
v___x_2959_ = lean_unsigned_to_nat(0u);
v_bs_x27_2960_ = lean_array_uset(v_bs_2945_, v_i_2944_, v___x_2959_);
v___x_2961_ = ((size_t)1ULL);
v___x_2962_ = lean_usize_add(v_i_2944_, v___x_2961_);
v___x_2963_ = lean_array_uset(v_bs_x27_2960_, v_i_2944_, v_a_2958_);
v_i_2944_ = v___x_2962_;
v_bs_2945_ = v___x_2963_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__10___boxed(lean_object* v_sz_2965_, lean_object* v_i_2966_, lean_object* v_bs_2967_){
_start:
{
size_t v_sz_boxed_2968_; size_t v_i_boxed_2969_; lean_object* v_res_2970_; 
v_sz_boxed_2968_ = lean_unbox_usize(v_sz_2965_);
lean_dec(v_sz_2965_);
v_i_boxed_2969_ = lean_unbox_usize(v_i_2966_);
lean_dec(v_i_2966_);
v_res_2970_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__10(v_sz_boxed_2968_, v_i_boxed_2969_, v_bs_2967_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6(lean_object* v_x_2971_){
_start:
{
if (lean_obj_tag(v_x_2971_) == 4)
{
lean_object* v_elems_2972_; size_t v_sz_2973_; size_t v___x_2974_; lean_object* v___x_2975_; 
v_elems_2972_ = lean_ctor_get(v_x_2971_, 0);
lean_inc_ref(v_elems_2972_);
lean_dec_ref_known(v_x_2971_, 1);
v_sz_2973_ = lean_array_size(v_elems_2972_);
v___x_2974_ = ((size_t)0ULL);
v___x_2975_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__10(v_sz_2973_, v___x_2974_, v_elems_2972_);
return v___x_2975_;
}
else
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2976_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0));
v___x_2977_ = lean_unsigned_to_nat(80u);
v___x_2978_ = l_Lean_Json_pretty(v_x_2971_, v___x_2977_);
v___x_2979_ = lean_string_append(v___x_2976_, v___x_2978_);
lean_dec_ref(v___x_2978_);
v___x_2980_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_2981_ = lean_string_append(v___x_2979_, v___x_2980_);
v___x_2982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2981_);
return v___x_2982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3(lean_object* v_j_2983_, lean_object* v_k_2984_){
_start:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = l_Lean_Json_getObjValD(v_j_2983_, v_k_2984_);
v___x_2986_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6(v___x_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3___boxed(lean_object* v_j_2987_, lean_object* v_k_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3(v_j_2987_, v_k_2988_);
lean_dec_ref(v_k_2988_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0(lean_object* v_x_2992_){
_start:
{
if (lean_obj_tag(v_x_2992_) == 0)
{
lean_object* v___x_2993_; 
v___x_2993_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0___closed__0));
return v___x_2993_;
}
else
{
lean_object* v___x_2994_; 
v___x_2994_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0(v_x_2992_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2994_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2994_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3011_; 
v_a_3003_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3005_ = v___x_2994_;
v_isShared_3006_ = v_isSharedCheck_3011_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2994_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3011_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3007_; lean_object* v___x_3009_; 
v___x_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3007_, 0, v_a_3003_);
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 0, v___x_3007_);
v___x_3009_ = v___x_3005_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3007_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0(lean_object* v_j_3012_, lean_object* v_k_3013_){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3014_ = l_Lean_Json_getObjValD(v_j_3012_, v_k_3013_);
v___x_3015_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0(v___x_3014_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0___boxed(lean_object* v_j_3016_, lean_object* v_k_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0(v_j_3016_, v_k_3017_);
lean_dec_ref(v_k_3017_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__7(size_t v_sz_3019_, size_t v_i_3020_, lean_object* v_bs_3021_){
_start:
{
uint8_t v___x_3022_; 
v___x_3022_ = lean_usize_dec_lt(v_i_3020_, v_sz_3019_);
if (v___x_3022_ == 0)
{
lean_object* v___x_3023_; 
v___x_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3023_, 0, v_bs_3021_);
return v___x_3023_;
}
else
{
lean_object* v_v_3024_; lean_object* v___x_3025_; 
v_v_3024_ = lean_array_uget_borrowed(v_bs_3021_, v_i_3020_);
lean_inc(v_v_3024_);
v___x_3025_ = l_Lean_Json_getStr_x3f(v_v_3024_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec_ref(v_bs_3021_);
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3025_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3025_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3035_; lean_object* v_bs_x27_3036_; size_t v___x_3037_; size_t v___x_3038_; lean_object* v___x_3039_; 
v_a_3034_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3034_);
lean_dec_ref_known(v___x_3025_, 1);
v___x_3035_ = lean_unsigned_to_nat(0u);
v_bs_x27_3036_ = lean_array_uset(v_bs_3021_, v_i_3020_, v___x_3035_);
v___x_3037_ = ((size_t)1ULL);
v___x_3038_ = lean_usize_add(v_i_3020_, v___x_3037_);
v___x_3039_ = lean_array_uset(v_bs_x27_3036_, v_i_3020_, v_a_3034_);
v_i_3020_ = v___x_3038_;
v_bs_3021_ = v___x_3039_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__7___boxed(lean_object* v_sz_3041_, lean_object* v_i_3042_, lean_object* v_bs_3043_){
_start:
{
size_t v_sz_boxed_3044_; size_t v_i_boxed_3045_; lean_object* v_res_3046_; 
v_sz_boxed_3044_ = lean_unbox_usize(v_sz_3041_);
lean_dec(v_sz_3041_);
v_i_boxed_3045_ = lean_unbox_usize(v_i_3042_);
lean_dec(v_i_3042_);
v_res_3046_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__7(v_sz_boxed_3044_, v_i_boxed_3045_, v_bs_3043_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4(lean_object* v_x_3047_){
_start:
{
if (lean_obj_tag(v_x_3047_) == 4)
{
lean_object* v_elems_3048_; size_t v_sz_3049_; size_t v___x_3050_; lean_object* v___x_3051_; 
v_elems_3048_ = lean_ctor_get(v_x_3047_, 0);
lean_inc_ref(v_elems_3048_);
lean_dec_ref_known(v_x_3047_, 1);
v_sz_3049_ = lean_array_size(v_elems_3048_);
v___x_3050_ = ((size_t)0ULL);
v___x_3051_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__7(v_sz_3049_, v___x_3050_, v_elems_3048_);
return v___x_3051_;
}
else
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3052_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0));
v___x_3053_ = lean_unsigned_to_nat(80u);
v___x_3054_ = l_Lean_Json_pretty(v_x_3047_, v___x_3053_);
v___x_3055_ = lean_string_append(v___x_3052_, v___x_3054_);
lean_dec_ref(v___x_3054_);
v___x_3056_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_3057_ = lean_string_append(v___x_3055_, v___x_3056_);
v___x_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3057_);
return v___x_3058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3_spec__7(size_t v_sz_3059_, size_t v_i_3060_, lean_object* v_bs_3061_){
_start:
{
uint8_t v___x_3062_; 
v___x_3062_ = lean_usize_dec_lt(v_i_3060_, v_sz_3059_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; 
v___x_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3063_, 0, v_bs_3061_);
return v___x_3063_;
}
else
{
lean_object* v_v_3064_; lean_object* v___x_3065_; 
v_v_3064_ = lean_array_uget_borrowed(v_bs_3061_, v_i_3060_);
lean_inc(v_v_3064_);
v___x_3065_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4(v_v_3064_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_dec_ref(v_bs_3061_);
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_3065_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3065_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3075_; lean_object* v_bs_x27_3076_; size_t v___x_3077_; size_t v___x_3078_; lean_object* v___x_3079_; 
v_a_3074_ = lean_ctor_get(v___x_3065_, 0);
lean_inc(v_a_3074_);
lean_dec_ref_known(v___x_3065_, 1);
v___x_3075_ = lean_unsigned_to_nat(0u);
v_bs_x27_3076_ = lean_array_uset(v_bs_3061_, v_i_3060_, v___x_3075_);
v___x_3077_ = ((size_t)1ULL);
v___x_3078_ = lean_usize_add(v_i_3060_, v___x_3077_);
v___x_3079_ = lean_array_uset(v_bs_x27_3076_, v_i_3060_, v_a_3074_);
v_i_3060_ = v___x_3078_;
v_bs_3061_ = v___x_3079_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3_spec__7___boxed(lean_object* v_sz_3081_, lean_object* v_i_3082_, lean_object* v_bs_3083_){
_start:
{
size_t v_sz_boxed_3084_; size_t v_i_boxed_3085_; lean_object* v_res_3086_; 
v_sz_boxed_3084_ = lean_unbox_usize(v_sz_3081_);
lean_dec(v_sz_3081_);
v_i_boxed_3085_ = lean_unbox_usize(v_i_3082_);
lean_dec(v_i_3082_);
v_res_3086_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3_spec__7(v_sz_boxed_3084_, v_i_boxed_3085_, v_bs_3083_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3(lean_object* v_x_3087_){
_start:
{
if (lean_obj_tag(v_x_3087_) == 4)
{
lean_object* v_elems_3088_; size_t v_sz_3089_; size_t v___x_3090_; lean_object* v___x_3091_; 
v_elems_3088_ = lean_ctor_get(v_x_3087_, 0);
lean_inc_ref(v_elems_3088_);
lean_dec_ref_known(v_x_3087_, 1);
v_sz_3089_ = lean_array_size(v_elems_3088_);
v___x_3090_ = ((size_t)0ULL);
v___x_3091_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3_spec__7(v_sz_3089_, v___x_3090_, v_elems_3088_);
return v___x_3091_;
}
else
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3092_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0));
v___x_3093_ = lean_unsigned_to_nat(80u);
v___x_3094_ = l_Lean_Json_pretty(v_x_3087_, v___x_3093_);
v___x_3095_ = lean_string_append(v___x_3092_, v___x_3094_);
lean_dec_ref(v___x_3094_);
v___x_3096_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_3097_ = lean_string_append(v___x_3095_, v___x_3096_);
v___x_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3097_);
return v___x_3098_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__4(lean_object* v_init_3099_, lean_object* v_x_3100_){
_start:
{
if (lean_obj_tag(v_x_3100_) == 0)
{
lean_object* v_k_3101_; lean_object* v_v_3102_; lean_object* v_l_3103_; lean_object* v_r_3104_; lean_object* v___x_3105_; 
v_k_3101_ = lean_ctor_get(v_x_3100_, 1);
lean_inc(v_k_3101_);
v_v_3102_ = lean_ctor_get(v_x_3100_, 2);
lean_inc(v_v_3102_);
v_l_3103_ = lean_ctor_get(v_x_3100_, 3);
lean_inc(v_l_3103_);
v_r_3104_ = lean_ctor_get(v_x_3100_, 4);
lean_inc(v_r_3104_);
lean_dec_ref_known(v_x_3100_, 5);
v___x_3105_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__4(v_init_3099_, v_l_3103_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_dec(v_r_3104_);
lean_dec(v_v_3102_);
lean_dec(v_k_3101_);
return v___x_3105_;
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3146_; 
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3108_ = v___x_3105_;
v_isShared_3109_ = v_isSharedCheck_3146_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3105_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3146_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3110_; uint8_t v___x_3111_; 
v___x_3110_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__2));
v___x_3111_ = lean_string_dec_eq(v_k_3101_, v___x_3110_);
if (v___x_3111_ == 0)
{
lean_object* v_n_3112_; uint8_t v___x_3113_; 
lean_inc(v_k_3101_);
v_n_3112_ = l_String_toName(v_k_3101_);
v___x_3113_ = l_Lean_Name_isAnonymous(v_n_3112_);
if (v___x_3113_ == 0)
{
lean_object* v___x_3114_; 
lean_del_object(v___x_3108_);
lean_dec(v_k_3101_);
v___x_3114_ = l_Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3(v_v_3102_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
lean_dec(v_n_3112_);
lean_dec(v_a_3106_);
lean_dec(v_r_3104_);
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_3114_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3114_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3124_; 
v_a_3123_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3123_);
lean_dec_ref_known(v___x_3114_, 1);
v___x_3124_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_3112_, v_a_3123_, v_a_3106_);
v_init_3099_ = v___x_3124_;
v_x_3100_ = v_r_3104_;
goto _start;
}
}
else
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3131_; 
lean_dec(v_n_3112_);
lean_dec(v_a_3106_);
lean_dec(v_r_3104_);
lean_dec(v_v_3102_);
v___x_3126_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__4));
v___x_3127_ = lean_string_append(v___x_3126_, v_k_3101_);
lean_dec(v_k_3101_);
v___x_3128_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_3129_ = lean_string_append(v___x_3127_, v___x_3128_);
if (v_isShared_3109_ == 0)
{
lean_ctor_set_tag(v___x_3108_, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3129_);
v___x_3131_ = v___x_3108_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v___x_3129_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
else
{
lean_object* v___x_3133_; 
lean_del_object(v___x_3108_);
lean_dec(v_k_3101_);
v___x_3133_ = l_Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3(v_v_3102_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
lean_dec(v_a_3106_);
lean_dec(v_r_3104_);
v_a_3134_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3136_ = v___x_3133_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3133_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
if (v_isShared_3137_ == 0)
{
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3134_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v_a_3142_ = lean_ctor_get(v___x_3133_, 0);
lean_inc(v_a_3142_);
lean_dec_ref_known(v___x_3133_, 1);
v___x_3143_ = lean_box(0);
v___x_3144_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_3143_, v_a_3142_, v_a_3106_);
v_init_3099_ = v___x_3144_;
v_x_3100_ = v_r_3104_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_3147_; 
v___x_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3147_, 0, v_init_3099_);
return v___x_3147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2(lean_object* v_x_3148_){
_start:
{
if (lean_obj_tag(v_x_3148_) == 5)
{
lean_object* v_kvPairs_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v_kvPairs_3149_ = lean_ctor_get(v_x_3148_, 0);
lean_inc(v_kvPairs_3149_);
lean_dec_ref_known(v_x_3148_, 1);
v___x_3150_ = lean_box(1);
v___x_3151_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__4(v___x_3150_, v_kvPairs_3149_);
return v___x_3151_;
}
else
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3152_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8___closed__0));
v___x_3153_ = lean_unsigned_to_nat(80u);
v___x_3154_ = l_Lean_Json_pretty(v_x_3148_, v___x_3153_);
v___x_3155_ = lean_string_append(v___x_3152_, v___x_3154_);
lean_dec_ref(v___x_3154_);
v___x_3156_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_3157_ = lean_string_append(v___x_3155_, v___x_3156_);
v___x_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
return v___x_3158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1(lean_object* v_j_3159_, lean_object* v_k_3160_){
_start:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3161_ = l_Lean_Json_getObjValD(v_j_3159_, v_k_3160_);
v___x_3162_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2(v___x_3161_);
return v___x_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1___boxed(lean_object* v_j_3163_, lean_object* v_k_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1(v_j_3163_, v_k_3164_);
lean_dec_ref(v_k_3164_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2(lean_object* v_j_3166_, lean_object* v_k_3167_){
_start:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3168_ = l_Lean_Json_getObjValD(v_j_3166_, v_k_3167_);
v___x_3169_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4(v___x_3168_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2___boxed(lean_object* v_j_3170_, lean_object* v_k_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2(v_j_3170_, v_k_3171_);
lean_dec_ref(v_k_3171_);
return v_res_3172_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3177_ = 1;
v___x_3178_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__1));
v___x_3179_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3178_, v___x_3177_);
return v___x_3179_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3180_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__4));
v___x_3181_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__2, &l_Lean_instFromJsonModuleSetup_fromJson___closed__2_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__2);
v___x_3182_ = lean_string_append(v___x_3181_, v___x_3180_);
return v___x_3182_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__5(void){
_start:
{
uint8_t v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3185_ = 1;
v___x_3186_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__4));
v___x_3187_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3186_, v___x_3185_);
return v___x_3187_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__6(void){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3188_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__5, &l_Lean_instFromJsonModuleSetup_fromJson___closed__5_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__5);
v___x_3189_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3190_ = lean_string_append(v___x_3189_, v___x_3188_);
return v___x_3190_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3191_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3192_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__6, &l_Lean_instFromJsonModuleSetup_fromJson___closed__6_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__6);
v___x_3193_ = lean_string_append(v___x_3192_, v___x_3191_);
return v___x_3193_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__9(void){
_start:
{
uint8_t v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3196_ = 1;
v___x_3197_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__8));
v___x_3198_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3197_, v___x_3196_);
return v___x_3198_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3199_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__9, &l_Lean_instFromJsonModuleSetup_fromJson___closed__9_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__9);
v___x_3200_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3201_ = lean_string_append(v___x_3200_, v___x_3199_);
return v___x_3201_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__11(void){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3202_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3203_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__10, &l_Lean_instFromJsonModuleSetup_fromJson___closed__10_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__10);
v___x_3204_ = lean_string_append(v___x_3203_, v___x_3202_);
return v___x_3204_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3205_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__9, &l_Lean_instFromJsonModuleHeader_fromJson___closed__9_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__9);
v___x_3206_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3207_ = lean_string_append(v___x_3206_, v___x_3205_);
return v___x_3207_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__13(void){
_start:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3208_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3209_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__12, &l_Lean_instFromJsonModuleSetup_fromJson___closed__12_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__12);
v___x_3210_ = lean_string_append(v___x_3209_, v___x_3208_);
return v___x_3210_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__15(void){
_start:
{
uint8_t v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3213_ = 1;
v___x_3214_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__14));
v___x_3215_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3214_, v___x_3213_);
return v___x_3215_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__16(void){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3216_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__15, &l_Lean_instFromJsonModuleSetup_fromJson___closed__15_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__15);
v___x_3217_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3218_ = lean_string_append(v___x_3217_, v___x_3216_);
return v___x_3218_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__17(void){
_start:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3219_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3220_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__16, &l_Lean_instFromJsonModuleSetup_fromJson___closed__16_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__16);
v___x_3221_ = lean_string_append(v___x_3220_, v___x_3219_);
return v___x_3221_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__19(void){
_start:
{
uint8_t v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3224_ = 1;
v___x_3225_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__18));
v___x_3226_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3225_, v___x_3224_);
return v___x_3226_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__20(void){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3227_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__19, &l_Lean_instFromJsonModuleSetup_fromJson___closed__19_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__19);
v___x_3228_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3229_ = lean_string_append(v___x_3228_, v___x_3227_);
return v___x_3229_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__21(void){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3230_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3231_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__20, &l_Lean_instFromJsonModuleSetup_fromJson___closed__20_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__20);
v___x_3232_ = lean_string_append(v___x_3231_, v___x_3230_);
return v___x_3232_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__23(void){
_start:
{
uint8_t v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3235_ = 1;
v___x_3236_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__22));
v___x_3237_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3236_, v___x_3235_);
return v___x_3237_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__24(void){
_start:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3238_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__23, &l_Lean_instFromJsonModuleSetup_fromJson___closed__23_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__23);
v___x_3239_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3240_ = lean_string_append(v___x_3239_, v___x_3238_);
return v___x_3240_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__25(void){
_start:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3241_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3242_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__24, &l_Lean_instFromJsonModuleSetup_fromJson___closed__24_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__24);
v___x_3243_ = lean_string_append(v___x_3242_, v___x_3241_);
return v___x_3243_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__27(void){
_start:
{
uint8_t v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3246_ = 1;
v___x_3247_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__26));
v___x_3248_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3247_, v___x_3246_);
return v___x_3248_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__28(void){
_start:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3249_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__27, &l_Lean_instFromJsonModuleSetup_fromJson___closed__27_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__27);
v___x_3250_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3251_ = lean_string_append(v___x_3250_, v___x_3249_);
return v___x_3251_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__29(void){
_start:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3252_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3253_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__28, &l_Lean_instFromJsonModuleSetup_fromJson___closed__28_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__28);
v___x_3254_ = lean_string_append(v___x_3253_, v___x_3252_);
return v___x_3254_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__31(void){
_start:
{
uint8_t v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3257_ = 1;
v___x_3258_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__30));
v___x_3259_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3258_, v___x_3257_);
return v___x_3259_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__32(void){
_start:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3260_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__31, &l_Lean_instFromJsonModuleSetup_fromJson___closed__31_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__31);
v___x_3261_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3262_ = lean_string_append(v___x_3261_, v___x_3260_);
return v___x_3262_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__33(void){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3263_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3264_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__32, &l_Lean_instFromJsonModuleSetup_fromJson___closed__32_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__32);
v___x_3265_ = lean_string_append(v___x_3264_, v___x_3263_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonModuleSetup_fromJson(lean_object* v_json_3266_){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3267_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__0));
lean_inc(v_json_3266_);
v___x_3268_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__0(v_json_3266_, v___x_3267_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3278_; 
lean_dec(v_json_3266_);
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3271_ = v___x_3268_;
v_isShared_3272_ = v_isSharedCheck_3278_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3268_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3278_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3276_; 
v___x_3273_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__7, &l_Lean_instFromJsonModuleSetup_fromJson___closed__7_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__7);
v___x_3274_ = lean_string_append(v___x_3273_, v_a_3269_);
lean_dec(v_a_3269_);
if (v_isShared_3272_ == 0)
{
lean_ctor_set(v___x_3271_, 0, v___x_3274_);
v___x_3276_ = v___x_3271_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3274_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
else
{
lean_object* v_a_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v_a_3279_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3279_);
lean_dec_ref_known(v___x_3268_, 1);
v___x_3280_ = ((lean_object*)(l_Lean_instToJsonModuleSetup_toJson___closed__0));
lean_inc(v_json_3266_);
v___x_3281_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1(v_json_3266_, v___x_3280_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3291_; 
lean_dec(v_a_3279_);
lean_dec(v_json_3266_);
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
v___x_3286_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__11, &l_Lean_instFromJsonModuleSetup_fromJson___closed__11_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__11);
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
v___x_3293_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__5));
lean_inc(v_json_3266_);
v___x_3294_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(v_json_3266_, v___x_3293_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3304_; 
lean_dec(v_a_3292_);
lean_dec(v_a_3279_);
lean_dec(v_json_3266_);
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
v___x_3299_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__13, &l_Lean_instFromJsonModuleSetup_fromJson___closed__13_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__13);
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
v___x_3306_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__0));
lean_inc(v_json_3266_);
v___x_3307_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0(v_json_3266_, v___x_3306_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3317_; 
lean_dec(v_a_3305_);
lean_dec(v_a_3292_);
lean_dec(v_a_3279_);
lean_dec(v_json_3266_);
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
v___x_3312_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__17, &l_Lean_instFromJsonModuleSetup_fromJson___closed__17_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__17);
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
v___x_3319_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__8));
lean_inc(v_json_3266_);
v___x_3320_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1(v_json_3266_, v___x_3319_);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3330_; 
lean_dec(v_a_3318_);
lean_dec(v_a_3305_);
lean_dec(v_a_3292_);
lean_dec(v_a_3279_);
lean_dec(v_json_3266_);
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
v___x_3325_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__21, &l_Lean_instFromJsonModuleSetup_fromJson___closed__21_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__21);
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
v___x_3332_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__12));
lean_inc(v_json_3266_);
v___x_3333_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2(v_json_3266_, v___x_3332_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3343_; 
lean_dec(v_a_3331_);
lean_dec(v_a_3318_);
lean_dec(v_a_3305_);
lean_dec(v_a_3292_);
lean_dec(v_a_3279_);
lean_dec(v_json_3266_);
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
v___x_3338_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__25, &l_Lean_instFromJsonModuleSetup_fromJson___closed__25_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__25);
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
v___x_3345_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__14));
lean_inc(v_json_3266_);
v___x_3346_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3(v_json_3266_, v___x_3345_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3356_; 
lean_dec(v_a_3344_);
lean_dec(v_a_3331_);
lean_dec(v_a_3318_);
lean_dec(v_a_3305_);
lean_dec(v_a_3292_);
lean_dec(v_a_3279_);
lean_dec(v_json_3266_);
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
v___x_3351_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__29, &l_Lean_instFromJsonModuleSetup_fromJson___closed__29_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__29);
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
v___x_3358_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__16));
v___x_3359_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4(v_json_3266_, v___x_3358_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3369_; 
lean_dec(v_a_3357_);
lean_dec(v_a_3344_);
lean_dec(v_a_3331_);
lean_dec(v_a_3318_);
lean_dec(v_a_3305_);
lean_dec(v_a_3292_);
lean_dec(v_a_3279_);
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
v___x_3364_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__33, &l_Lean_instFromJsonModuleSetup_fromJson___closed__33_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__33);
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
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3379_; 
v_a_3370_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3372_ = v___x_3359_;
v_isShared_3373_ = v_isSharedCheck_3379_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3359_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3379_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3374_; uint8_t v___x_3375_; lean_object* v___x_3377_; 
v___x_3374_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3374_, 0, v_a_3279_);
lean_ctor_set(v___x_3374_, 1, v_a_3292_);
lean_ctor_set(v___x_3374_, 2, v_a_3318_);
lean_ctor_set(v___x_3374_, 3, v_a_3331_);
lean_ctor_set(v___x_3374_, 4, v_a_3344_);
lean_ctor_set(v___x_3374_, 5, v_a_3357_);
lean_ctor_set(v___x_3374_, 6, v_a_3370_);
v___x_3375_ = lean_unbox(v_a_3305_);
lean_dec(v_a_3305_);
lean_ctor_set_uint8(v___x_3374_, sizeof(void*)*7, v___x_3375_);
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 0, v___x_3374_);
v___x_3377_ = v___x_3372_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3374_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
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
LEAN_EXPORT lean_object* l_Lean_ModuleSetup_load(lean_object* v_path_3383_){
_start:
{
lean_object* v___x_3385_; 
v___x_3385_ = l_IO_FS_readFile(v_path_3383_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3414_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3388_ = v___x_3385_;
v_isShared_3389_ = v_isSharedCheck_3414_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3385_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3414_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v_a_3391_; lean_object* v___x_3401_; 
v___x_3401_ = l_Lean_Json_parse(v_a_3386_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v_a_3402_; 
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_a_3402_);
lean_dec_ref_known(v___x_3401_, 1);
v_a_3391_ = v_a_3402_;
goto v___jp_3390_;
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3404_; 
v_a_3403_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_a_3403_);
lean_dec_ref_known(v___x_3401_, 1);
v___x_3404_ = l_Lean_instFromJsonModuleSetup_fromJson(v_a_3403_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_a_3405_);
lean_dec_ref_known(v___x_3404_, 1);
v_a_3391_ = v_a_3405_;
goto v___jp_3390_;
}
else
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
lean_del_object(v___x_3388_);
v_a_3406_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3404_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3404_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
lean_ctor_set_tag(v___x_3408_, 0);
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
}
v___jp_3390_:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3399_; 
v___x_3392_ = ((lean_object*)(l_Lean_ModuleSetup_load___closed__0));
v___x_3393_ = lean_string_append(v___x_3392_, v_path_3383_);
v___x_3394_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3395_ = lean_string_append(v___x_3393_, v___x_3394_);
v___x_3396_ = lean_string_append(v___x_3395_, v_a_3391_);
lean_dec_ref(v_a_3391_);
v___x_3397_ = lean_mk_io_user_error(v___x_3396_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set_tag(v___x_3388_, 1);
lean_ctor_set(v___x_3388_, 0, v___x_3397_);
v___x_3399_ = v___x_3388_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3397_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
v_a_3415_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3385_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3385_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleSetup_load___boxed(lean_object* v_path_3423_, lean_object* v_a_3424_){
_start:
{
lean_object* v_res_3425_; 
v_res_3425_ = l_Lean_ModuleSetup_load(v_path_3423_);
lean_dec_ref(v_path_3423_);
return v_res_3425_;
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
