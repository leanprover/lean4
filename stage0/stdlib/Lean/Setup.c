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
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
lean_dec(v_json_222_);
v_a_235_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_224_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_224_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
lean_ctor_set_tag(v___x_237_, 0);
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_235_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
else
{
lean_object* v_a_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_a_243_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_243_);
lean_dec_ref_known(v___x_224_, 1);
v___x_244_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__10));
lean_inc(v_json_222_);
v___x_245_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(v_json_222_, v___x_244_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_255_; 
lean_dec(v_a_243_);
lean_dec(v_json_222_);
v_a_246_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_255_ == 0)
{
v___x_248_ = v___x_245_;
v_isShared_249_ = v_isSharedCheck_255_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_245_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_255_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_250_ = lean_obj_once(&l_Lean_instFromJsonImport_fromJson___closed__14, &l_Lean_instFromJsonImport_fromJson___closed__14_once, _init_l_Lean_instFromJsonImport_fromJson___closed__14);
v___x_251_ = lean_string_append(v___x_250_, v_a_246_);
lean_dec(v_a_246_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_251_);
v___x_253_ = v___x_248_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
else
{
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
lean_dec(v_a_243_);
lean_dec(v_json_222_);
v_a_256_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_245_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_245_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
lean_ctor_set_tag(v___x_258_, 0);
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_a_264_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_a_264_);
lean_dec_ref_known(v___x_245_, 1);
v___x_265_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__13));
lean_inc(v_json_222_);
v___x_266_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(v_json_222_, v___x_265_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_276_; 
lean_dec(v_a_264_);
lean_dec(v_a_243_);
lean_dec(v_json_222_);
v_a_267_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_276_ == 0)
{
v___x_269_ = v___x_266_;
v_isShared_270_ = v_isSharedCheck_276_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_266_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_276_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_271_ = lean_obj_once(&l_Lean_instFromJsonImport_fromJson___closed__18, &l_Lean_instFromJsonImport_fromJson___closed__18_once, _init_l_Lean_instFromJsonImport_fromJson___closed__18);
v___x_272_ = lean_string_append(v___x_271_, v_a_267_);
lean_dec(v_a_267_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_272_);
v___x_274_ = v___x_269_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
else
{
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
lean_dec(v_a_264_);
lean_dec(v_a_243_);
lean_dec(v_json_222_);
v_a_277_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_266_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_266_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
lean_ctor_set_tag(v___x_279_, 0);
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
else
{
lean_object* v_a_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v_a_285_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_a_285_);
lean_dec_ref_known(v___x_266_, 1);
v___x_286_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__16));
v___x_287_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(v_json_222_, v___x_286_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_297_; 
lean_dec(v_a_285_);
lean_dec(v_a_264_);
lean_dec(v_a_243_);
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_297_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_297_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_297_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_292_ = lean_obj_once(&l_Lean_instFromJsonImport_fromJson___closed__22, &l_Lean_instFromJsonImport_fromJson___closed__22_once, _init_l_Lean_instFromJsonImport_fromJson___closed__22);
v___x_293_ = lean_string_append(v___x_292_, v_a_288_);
lean_dec(v_a_288_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_293_);
v___x_295_ = v___x_290_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
else
{
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec(v_a_285_);
lean_dec(v_a_264_);
lean_dec(v_a_243_);
v_a_298_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_287_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_287_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set_tag(v___x_300_, 0);
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
else
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_317_; 
v_a_306_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_317_ == 0)
{
v___x_308_ = v___x_287_;
v_isShared_309_ = v_isSharedCheck_317_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_287_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_317_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; uint8_t v___x_311_; uint8_t v___x_312_; uint8_t v___x_313_; lean_object* v___x_315_; 
v___x_310_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_310_, 0, v_a_243_);
v___x_311_ = lean_unbox(v_a_264_);
lean_dec(v_a_264_);
lean_ctor_set_uint8(v___x_310_, sizeof(void*)*1, v___x_311_);
v___x_312_ = lean_unbox(v_a_285_);
lean_dec(v_a_285_);
lean_ctor_set_uint8(v___x_310_, sizeof(void*)*1 + 1, v___x_312_);
v___x_313_ = lean_unbox(v_a_306_);
lean_dec(v_a_306_);
lean_ctor_set_uint8(v___x_310_, sizeof(void*)*1 + 2, v___x_313_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_310_);
v___x_315_ = v___x_308_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_310_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
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
LEAN_EXPORT uint8_t l_Lean_instBEqImport_beq(lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
lean_object* v_module_322_; uint8_t v_importAll_323_; uint8_t v_isExported_324_; uint8_t v_isMeta_325_; lean_object* v_module_326_; uint8_t v_importAll_327_; uint8_t v_isExported_328_; uint8_t v_isMeta_329_; uint8_t v___y_331_; uint8_t v___y_333_; uint8_t v___x_334_; 
v_module_322_ = lean_ctor_get(v_x_320_, 0);
v_importAll_323_ = lean_ctor_get_uint8(v_x_320_, sizeof(void*)*1);
v_isExported_324_ = lean_ctor_get_uint8(v_x_320_, sizeof(void*)*1 + 1);
v_isMeta_325_ = lean_ctor_get_uint8(v_x_320_, sizeof(void*)*1 + 2);
v_module_326_ = lean_ctor_get(v_x_321_, 0);
v_importAll_327_ = lean_ctor_get_uint8(v_x_321_, sizeof(void*)*1);
v_isExported_328_ = lean_ctor_get_uint8(v_x_321_, sizeof(void*)*1 + 1);
v_isMeta_329_ = lean_ctor_get_uint8(v_x_321_, sizeof(void*)*1 + 2);
v___x_334_ = lean_name_eq(v_module_322_, v_module_326_);
if (v___x_334_ == 0)
{
return v___x_334_;
}
else
{
if (v_importAll_327_ == 0)
{
if (v_importAll_323_ == 0)
{
v___y_333_ = v___x_334_;
goto v___jp_332_;
}
else
{
return v_importAll_327_;
}
}
else
{
v___y_333_ = v_importAll_323_;
goto v___jp_332_;
}
}
v___jp_330_:
{
if (v_isMeta_329_ == 0)
{
if (v_isMeta_325_ == 0)
{
return v___y_331_;
}
else
{
return v_isMeta_329_;
}
}
else
{
return v_isMeta_325_;
}
}
v___jp_332_:
{
if (v___y_333_ == 0)
{
return v___y_333_;
}
else
{
if (v_isExported_328_ == 0)
{
if (v_isExported_324_ == 0)
{
v___y_331_ = v___y_333_;
goto v___jp_330_;
}
else
{
return v_isExported_328_;
}
}
else
{
if (v_isExported_324_ == 0)
{
return v_isExported_324_;
}
else
{
v___y_331_ = v_isExported_324_;
goto v___jp_330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqImport_beq___boxed(lean_object* v_x_335_, lean_object* v_x_336_){
_start:
{
uint8_t v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l_Lean_instBEqImport_beq(v_x_335_, v_x_336_);
lean_dec_ref(v_x_336_);
lean_dec_ref(v_x_335_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableImport_hash(lean_object* v_x_341_){
_start:
{
lean_object* v_module_342_; uint8_t v_importAll_343_; uint8_t v_isExported_344_; uint8_t v_isMeta_345_; uint64_t v___y_347_; uint64_t v___y_348_; uint64_t v___y_355_; uint64_t v___y_356_; uint64_t v___x_360_; uint64_t v___y_362_; 
v_module_342_ = lean_ctor_get(v_x_341_, 0);
v_importAll_343_ = lean_ctor_get_uint8(v_x_341_, sizeof(void*)*1);
v_isExported_344_ = lean_ctor_get_uint8(v_x_341_, sizeof(void*)*1 + 1);
v_isMeta_345_ = lean_ctor_get_uint8(v_x_341_, sizeof(void*)*1 + 2);
v___x_360_ = 0ULL;
if (lean_obj_tag(v_module_342_) == 0)
{
uint64_t v___x_366_; 
v___x_366_ = 1723ULL;
v___y_362_ = v___x_366_;
goto v___jp_361_;
}
else
{
uint64_t v_hash_367_; 
v_hash_367_ = lean_ctor_get_uint64(v_module_342_, sizeof(void*)*2);
v___y_362_ = v_hash_367_;
goto v___jp_361_;
}
v___jp_346_:
{
uint64_t v___x_349_; 
v___x_349_ = lean_uint64_mix_hash(v___y_347_, v___y_348_);
if (v_isMeta_345_ == 0)
{
uint64_t v___x_350_; uint64_t v___x_351_; 
v___x_350_ = 13ULL;
v___x_351_ = lean_uint64_mix_hash(v___x_349_, v___x_350_);
return v___x_351_;
}
else
{
uint64_t v___x_352_; uint64_t v___x_353_; 
v___x_352_ = 11ULL;
v___x_353_ = lean_uint64_mix_hash(v___x_349_, v___x_352_);
return v___x_353_;
}
}
v___jp_354_:
{
uint64_t v___x_357_; 
v___x_357_ = lean_uint64_mix_hash(v___y_355_, v___y_356_);
if (v_isExported_344_ == 0)
{
uint64_t v___x_358_; 
v___x_358_ = 13ULL;
v___y_347_ = v___x_357_;
v___y_348_ = v___x_358_;
goto v___jp_346_;
}
else
{
uint64_t v___x_359_; 
v___x_359_ = 11ULL;
v___y_347_ = v___x_357_;
v___y_348_ = v___x_359_;
goto v___jp_346_;
}
}
v___jp_361_:
{
uint64_t v___x_363_; 
v___x_363_ = lean_uint64_mix_hash(v___x_360_, v___y_362_);
if (v_importAll_343_ == 0)
{
uint64_t v___x_364_; 
v___x_364_ = 13ULL;
v___y_355_ = v___x_363_;
v___y_356_ = v___x_364_;
goto v___jp_354_;
}
else
{
uint64_t v___x_365_; 
v___x_365_ = 11ULL;
v___y_355_ = v___x_363_;
v___y_356_ = v___x_365_;
goto v___jp_354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableImport_hash___boxed(lean_object* v_x_368_){
_start:
{
uint64_t v_res_369_; lean_object* v_r_370_; 
v_res_369_ = l_Lean_instHashableImport_hash(v_x_368_);
lean_dec_ref(v_x_368_);
v_r_370_ = lean_box_uint64(v_res_369_);
return v_r_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Idbg_idbgClientLoop___boxed(lean_object* v_00_u03b1_379_, lean_object* v_inst_00___x40_Lean_Setup_1068012781____hygCtx___hyg_380_, lean_object* v_siteId_381_, lean_object* v_imports_382_, lean_object* v_apply_383_, lean_object* v_a_00___x40___internal___hyg_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = lean_idbg_client_loop(v_siteId_381_, v_imports_382_, v_apply_383_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeNameImport___lam__0(lean_object* v_x_386_){
_start:
{
uint8_t v___x_387_; uint8_t v___x_388_; lean_object* v___x_389_; 
v___x_387_ = 0;
v___x_388_ = 1;
v___x_389_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_389_, 0, v_x_386_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*1, v___x_387_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*1 + 1, v___x_388_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*1 + 2, v___x_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringImport___lam__0(lean_object* v_imp_397_){
_start:
{
lean_object* v_module_398_; uint8_t v_importAll_399_; uint8_t v_isExported_400_; uint8_t v_isMeta_401_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_418_; 
v_module_398_ = lean_ctor_get(v_imp_397_, 0);
lean_inc(v_module_398_);
v_importAll_399_ = lean_ctor_get_uint8(v_imp_397_, sizeof(void*)*1);
v_isExported_400_ = lean_ctor_get_uint8(v_imp_397_, sizeof(void*)*1 + 1);
v_isMeta_401_ = lean_ctor_get_uint8(v_imp_397_, sizeof(void*)*1 + 2);
lean_dec_ref(v_imp_397_);
if (v_isExported_400_ == 0)
{
lean_object* v___x_421_; 
v___x_421_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__1));
v___y_418_ = v___x_421_;
goto v___jp_417_;
}
else
{
lean_object* v___x_422_; 
v___x_422_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__4));
v___y_418_ = v___x_422_;
goto v___jp_417_;
}
v___jp_402_:
{
lean_object* v___x_405_; uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_405_ = lean_string_append(v___y_403_, v___y_404_);
v___x_406_ = 1;
v___x_407_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_398_, v___x_406_);
v___x_408_ = lean_string_append(v___x_405_, v___x_407_);
lean_dec_ref(v___x_407_);
return v___x_408_;
}
v___jp_409_:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
lean_inc_ref(v___y_410_);
v___x_412_ = lean_string_append(v___y_410_, v___y_411_);
v___x_413_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__0));
v___x_414_ = lean_string_append(v___x_412_, v___x_413_);
if (v_importAll_399_ == 0)
{
lean_object* v___x_415_; 
v___x_415_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__1));
v___y_403_ = v___x_414_;
v___y_404_ = v___x_415_;
goto v___jp_402_;
}
else
{
lean_object* v___x_416_; 
v___x_416_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__2));
v___y_403_ = v___x_414_;
v___y_404_ = v___x_416_;
goto v___jp_402_;
}
}
v___jp_417_:
{
if (v_isMeta_401_ == 0)
{
lean_object* v___x_419_; 
v___x_419_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__1));
v___y_410_ = v___y_418_;
v___y_411_ = v___x_419_;
goto v___jp_409_;
}
else
{
lean_object* v___x_420_; 
v___x_420_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__3));
v___y_410_ = v___y_418_;
v___y_411_ = v___x_420_;
goto v___jp_409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorIdx___impl(uint8_t v_x_425_){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_box(v_x_425_);
v___x_427_ = lean_obj_tag_nat(v___x_426_);
lean_dec(v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorIdx___impl___boxed(lean_object* v_x_428_){
_start:
{
uint8_t v_x_4__boxed_429_; lean_object* v_res_430_; 
v_x_4__boxed_429_ = lean_unbox(v_x_428_);
v_res_430_ = l_Lean_IRPhases_ctorIdx___impl(v_x_4__boxed_429_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorElim___redArg(lean_object* v_k_431_){
_start:
{
lean_inc(v_k_431_);
return v_k_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorElim___redArg___boxed(lean_object* v_k_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_IRPhases_ctorElim___redArg(v_k_432_);
lean_dec(v_k_432_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorElim(lean_object* v_motive_434_, lean_object* v_ctorIdx_435_, uint8_t v_t_436_, lean_object* v_h_437_, lean_object* v_k_438_){
_start:
{
lean_inc(v_k_438_);
return v_k_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorElim___boxed(lean_object* v_motive_439_, lean_object* v_ctorIdx_440_, lean_object* v_t_441_, lean_object* v_h_442_, lean_object* v_k_443_){
_start:
{
uint8_t v_t_boxed_444_; lean_object* v_res_445_; 
v_t_boxed_444_ = lean_unbox(v_t_441_);
v_res_445_ = l_Lean_IRPhases_ctorElim(v_motive_439_, v_ctorIdx_440_, v_t_boxed_444_, v_h_442_, v_k_443_);
lean_dec(v_k_443_);
lean_dec(v_ctorIdx_440_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_runtime_elim___redArg(lean_object* v_runtime_446_){
_start:
{
lean_inc(v_runtime_446_);
return v_runtime_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_runtime_elim___redArg___boxed(lean_object* v_runtime_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_IRPhases_runtime_elim___redArg(v_runtime_447_);
lean_dec(v_runtime_447_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_runtime_elim(lean_object* v_motive_449_, uint8_t v_t_450_, lean_object* v_h_451_, lean_object* v_runtime_452_){
_start:
{
lean_inc(v_runtime_452_);
return v_runtime_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_runtime_elim___boxed(lean_object* v_motive_453_, lean_object* v_t_454_, lean_object* v_h_455_, lean_object* v_runtime_456_){
_start:
{
uint8_t v_t_boxed_457_; lean_object* v_res_458_; 
v_t_boxed_457_ = lean_unbox(v_t_454_);
v_res_458_ = l_Lean_IRPhases_runtime_elim(v_motive_453_, v_t_boxed_457_, v_h_455_, v_runtime_456_);
lean_dec(v_runtime_456_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_comptime_elim___redArg(lean_object* v_comptime_459_){
_start:
{
lean_inc(v_comptime_459_);
return v_comptime_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_comptime_elim___redArg___boxed(lean_object* v_comptime_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_IRPhases_comptime_elim___redArg(v_comptime_460_);
lean_dec(v_comptime_460_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_comptime_elim(lean_object* v_motive_462_, uint8_t v_t_463_, lean_object* v_h_464_, lean_object* v_comptime_465_){
_start:
{
lean_inc(v_comptime_465_);
return v_comptime_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_comptime_elim___boxed(lean_object* v_motive_466_, lean_object* v_t_467_, lean_object* v_h_468_, lean_object* v_comptime_469_){
_start:
{
uint8_t v_t_boxed_470_; lean_object* v_res_471_; 
v_t_boxed_470_ = lean_unbox(v_t_467_);
v_res_471_ = l_Lean_IRPhases_comptime_elim(v_motive_466_, v_t_boxed_470_, v_h_468_, v_comptime_469_);
lean_dec(v_comptime_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_all_elim___redArg(lean_object* v_all_472_){
_start:
{
lean_inc(v_all_472_);
return v_all_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_all_elim___redArg___boxed(lean_object* v_all_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_IRPhases_all_elim___redArg(v_all_473_);
lean_dec(v_all_473_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_all_elim(lean_object* v_motive_475_, uint8_t v_t_476_, lean_object* v_h_477_, lean_object* v_all_478_){
_start:
{
lean_inc(v_all_478_);
return v_all_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_all_elim___boxed(lean_object* v_motive_479_, lean_object* v_t_480_, lean_object* v_h_481_, lean_object* v_all_482_){
_start:
{
uint8_t v_t_boxed_483_; lean_object* v_res_484_; 
v_t_boxed_483_ = lean_unbox(v_t_480_);
v_res_484_ = l_Lean_IRPhases_all_elim(v_motive_479_, v_t_boxed_483_, v_h_481_, v_all_482_);
lean_dec(v_all_482_);
return v_res_484_;
}
}
static uint8_t _init_l_Lean_instInhabitedIRPhases_default(void){
_start:
{
uint8_t v___x_485_; 
v___x_485_ = 0;
return v___x_485_;
}
}
static uint8_t _init_l_Lean_instInhabitedIRPhases(void){
_start:
{
uint8_t v___x_486_; 
v___x_486_ = 0;
return v___x_486_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqIRPhases_beq(uint8_t v_x_487_, uint8_t v_y_488_){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_489_ = lean_box(v_x_487_);
v___x_490_ = lean_obj_tag_nat(v___x_489_);
lean_dec(v___x_489_);
v___x_491_ = lean_box(v_y_488_);
v___x_492_ = lean_obj_tag_nat(v___x_491_);
lean_dec(v___x_491_);
v___x_493_ = lean_nat_dec_eq(v___x_490_, v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqIRPhases_beq___boxed(lean_object* v_x_494_, lean_object* v_y_495_){
_start:
{
uint8_t v_x_24__boxed_496_; uint8_t v_y_25__boxed_497_; uint8_t v_res_498_; lean_object* v_r_499_; 
v_x_24__boxed_496_ = lean_unbox(v_x_494_);
v_y_25__boxed_497_ = lean_unbox(v_y_495_);
v_res_498_ = l_Lean_instBEqIRPhases_beq(v_x_24__boxed_496_, v_y_25__boxed_497_);
v_r_499_ = lean_box(v_res_498_);
return v_r_499_;
}
}
static lean_object* _init_l_Lean_instReprIRPhases_repr___closed__6(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_unsigned_to_nat(2u);
v___x_512_ = lean_nat_to_int(v___x_511_);
return v___x_512_;
}
}
static lean_object* _init_l_Lean_instReprIRPhases_repr___closed__7(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = lean_nat_to_int(v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprIRPhases_repr(uint8_t v_x_515_, lean_object* v_prec_516_){
_start:
{
lean_object* v___y_518_; lean_object* v___y_525_; lean_object* v___y_532_; 
switch(v_x_515_)
{
case 0:
{
lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_538_ = lean_unsigned_to_nat(1024u);
v___x_539_ = lean_nat_dec_le(v___x_538_, v_prec_516_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; 
v___x_540_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__6, &l_Lean_instReprIRPhases_repr___closed__6_once, _init_l_Lean_instReprIRPhases_repr___closed__6);
v___y_518_ = v___x_540_;
goto v___jp_517_;
}
else
{
lean_object* v___x_541_; 
v___x_541_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__7, &l_Lean_instReprIRPhases_repr___closed__7_once, _init_l_Lean_instReprIRPhases_repr___closed__7);
v___y_518_ = v___x_541_;
goto v___jp_517_;
}
}
case 1:
{
lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_542_ = lean_unsigned_to_nat(1024u);
v___x_543_ = lean_nat_dec_le(v___x_542_, v_prec_516_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; 
v___x_544_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__6, &l_Lean_instReprIRPhases_repr___closed__6_once, _init_l_Lean_instReprIRPhases_repr___closed__6);
v___y_525_ = v___x_544_;
goto v___jp_524_;
}
else
{
lean_object* v___x_545_; 
v___x_545_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__7, &l_Lean_instReprIRPhases_repr___closed__7_once, _init_l_Lean_instReprIRPhases_repr___closed__7);
v___y_525_ = v___x_545_;
goto v___jp_524_;
}
}
default: 
{
lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_546_ = lean_unsigned_to_nat(1024u);
v___x_547_ = lean_nat_dec_le(v___x_546_, v_prec_516_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; 
v___x_548_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__6, &l_Lean_instReprIRPhases_repr___closed__6_once, _init_l_Lean_instReprIRPhases_repr___closed__6);
v___y_532_ = v___x_548_;
goto v___jp_531_;
}
else
{
lean_object* v___x_549_; 
v___x_549_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__7, &l_Lean_instReprIRPhases_repr___closed__7_once, _init_l_Lean_instReprIRPhases_repr___closed__7);
v___y_532_ = v___x_549_;
goto v___jp_531_;
}
}
}
v___jp_517_:
{
lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_519_ = ((lean_object*)(l_Lean_instReprIRPhases_repr___closed__1));
lean_inc(v___y_518_);
v___x_520_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_520_, 0, v___y_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = 0;
v___x_522_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*1, v___x_521_);
v___x_523_ = l_Repr_addAppParen(v___x_522_, v_prec_516_);
return v___x_523_;
}
v___jp_524_:
{
lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_526_ = ((lean_object*)(l_Lean_instReprIRPhases_repr___closed__3));
lean_inc(v___y_525_);
v___x_527_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_527_, 0, v___y_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = 0;
v___x_529_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*1, v___x_528_);
v___x_530_ = l_Repr_addAppParen(v___x_529_, v_prec_516_);
return v___x_530_;
}
v___jp_531_:
{
lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_533_ = ((lean_object*)(l_Lean_instReprIRPhases_repr___closed__5));
lean_inc(v___y_532_);
v___x_534_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_534_, 0, v___y_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = 0;
v___x_536_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*1, v___x_535_);
v___x_537_ = l_Repr_addAppParen(v___x_536_, v_prec_516_);
return v___x_537_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprIRPhases_repr___boxed(lean_object* v_x_550_, lean_object* v_prec_551_){
_start:
{
uint8_t v_x_171__boxed_552_; lean_object* v_res_553_; 
v_x_171__boxed_552_ = lean_unbox(v_x_550_);
v_res_553_ = l_Lean_instReprIRPhases_repr(v_x_171__boxed_552_, v_prec_551_);
lean_dec(v_prec_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_556_, lean_object* v_x_557_, lean_object* v_x_558_){
_start:
{
if (lean_obj_tag(v_x_558_) == 0)
{
lean_dec(v_x_556_);
return v_x_557_;
}
else
{
lean_object* v_head_559_; lean_object* v_tail_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_570_; 
v_head_559_ = lean_ctor_get(v_x_558_, 0);
v_tail_560_ = lean_ctor_get(v_x_558_, 1);
v_isSharedCheck_570_ = !lean_is_exclusive(v_x_558_);
if (v_isSharedCheck_570_ == 0)
{
v___x_562_ = v_x_558_;
v_isShared_563_ = v_isSharedCheck_570_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_tail_560_);
lean_inc(v_head_559_);
lean_dec(v_x_558_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_570_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
lean_inc(v_x_556_);
if (v_isShared_563_ == 0)
{
lean_ctor_set_tag(v___x_562_, 5);
lean_ctor_set(v___x_562_, 1, v_x_556_);
lean_ctor_set(v___x_562_, 0, v_x_557_);
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_x_557_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_x_556_);
v___x_565_ = v_reuseFailAlloc_569_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = l_Lean_instReprImport_repr___redArg(v_head_559_);
v___x_567_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_565_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v_x_557_ = v___x_567_;
v_x_558_ = v_tail_560_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0_spec__1(lean_object* v_x_571_, lean_object* v_x_572_, lean_object* v_x_573_){
_start:
{
if (lean_obj_tag(v_x_573_) == 0)
{
lean_dec(v_x_571_);
return v_x_572_;
}
else
{
lean_object* v_head_574_; lean_object* v_tail_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_585_; 
v_head_574_ = lean_ctor_get(v_x_573_, 0);
v_tail_575_ = lean_ctor_get(v_x_573_, 1);
v_isSharedCheck_585_ = !lean_is_exclusive(v_x_573_);
if (v_isSharedCheck_585_ == 0)
{
v___x_577_ = v_x_573_;
v_isShared_578_ = v_isSharedCheck_585_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_tail_575_);
lean_inc(v_head_574_);
lean_dec(v_x_573_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_585_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
lean_inc(v_x_571_);
if (v_isShared_578_ == 0)
{
lean_ctor_set_tag(v___x_577_, 5);
lean_ctor_set(v___x_577_, 1, v_x_571_);
lean_ctor_set(v___x_577_, 0, v_x_572_);
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_x_572_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_x_571_);
v___x_580_ = v_reuseFailAlloc_584_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_581_ = l_Lean_instReprImport_repr___redArg(v_head_574_);
v___x_582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_580_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0_spec__1_spec__2(v_x_571_, v___x_582_, v_tail_575_);
return v___x_583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0(lean_object* v_x_586_, lean_object* v_x_587_){
_start:
{
if (lean_obj_tag(v_x_586_) == 0)
{
lean_object* v___x_588_; 
lean_dec(v_x_587_);
v___x_588_ = lean_box(0);
return v___x_588_;
}
else
{
lean_object* v_tail_589_; 
v_tail_589_ = lean_ctor_get(v_x_586_, 1);
if (lean_obj_tag(v_tail_589_) == 0)
{
lean_object* v_head_590_; lean_object* v___x_591_; 
lean_dec(v_x_587_);
v_head_590_ = lean_ctor_get(v_x_586_, 0);
lean_inc(v_head_590_);
lean_dec_ref_known(v_x_586_, 2);
v___x_591_ = l_Lean_instReprImport_repr___redArg(v_head_590_);
return v___x_591_;
}
else
{
lean_object* v_head_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
lean_inc(v_tail_589_);
v_head_592_ = lean_ctor_get(v_x_586_, 0);
lean_inc(v_head_592_);
lean_dec_ref_known(v_x_586_, 2);
v___x_593_ = l_Lean_instReprImport_repr___redArg(v_head_592_);
v___x_594_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0_spec__1(v_x_587_, v___x_593_, v_tail_589_);
return v___x_594_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__0));
v___x_601_ = lean_string_length(v___x_600_);
return v___x_601_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_obj_once(&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3, &l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3);
v___x_603_ = lean_nat_to_int(v___x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0(lean_object* v_xs_611_){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_612_ = lean_array_get_size(v_xs_611_);
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = lean_nat_dec_eq(v___x_612_, v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_615_ = lean_array_to_list(v_xs_611_);
v___x_616_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_617_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0(v___x_615_, v___x_616_);
v___x_618_ = lean_obj_once(&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4);
v___x_619_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5));
v___x_620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v___x_617_);
v___x_621_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6));
v___x_622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_618_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = l_Std_Format_fill(v___x_623_);
return v___x_624_;
}
else
{
lean_object* v___x_625_; 
lean_dec_ref(v_xs_611_);
v___x_625_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8));
return v___x_625_;
}
}
}
static lean_object* _init_l_Lean_instReprModuleHeader_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_unsigned_to_nat(11u);
v___x_636_ = lean_nat_to_int(v___x_635_);
return v___x_636_;
}
}
static lean_object* _init_l_Lean_instReprModuleHeader_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_unsigned_to_nat(12u);
v___x_641_ = lean_nat_to_int(v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleHeader_repr___redArg(lean_object* v_x_642_){
_start:
{
lean_object* v_imports_643_; uint8_t v_isModule_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_677_; 
v_imports_643_ = lean_ctor_get(v_x_642_, 0);
v_isModule_644_ = lean_ctor_get_uint8(v_x_642_, sizeof(void*)*1);
v_isSharedCheck_677_ = !lean_is_exclusive(v_x_642_);
if (v_isSharedCheck_677_ == 0)
{
v___x_646_ = v_x_642_;
v_isShared_647_ = v_isSharedCheck_677_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_imports_643_);
lean_dec(v_x_642_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_677_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; lean_object* v___x_655_; 
v___x_648_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__5));
v___x_649_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__3));
v___x_650_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__4, &l_Lean_instReprModuleHeader_repr___redArg___closed__4_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__4);
v___x_651_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0(v_imports_643_);
v___x_652_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_650_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = 0;
if (v_isShared_647_ == 0)
{
lean_ctor_set_tag(v___x_646_, 6);
lean_ctor_set(v___x_646_, 0, v___x_652_);
v___x_655_ = v___x_646_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_652_);
v___x_655_ = v_reuseFailAlloc_676_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*1, v___x_653_);
v___x_656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_649_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__9));
v___x_658_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_656_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = lean_box(1);
v___x_660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_658_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__6));
v___x_662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
lean_ctor_set(v___x_663_, 1, v___x_648_);
v___x_664_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__7, &l_Lean_instReprModuleHeader_repr___redArg___closed__7_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__7);
v___x_665_ = l_Bool_repr___redArg(v_isModule_644_);
v___x_666_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_664_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_667_, 0, v___x_666_);
lean_ctor_set_uint8(v___x_667_, sizeof(void*)*1, v___x_653_);
v___x_668_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_663_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__20, &l_Lean_instReprImport_repr___redArg___closed__20_once, _init_l_Lean_instReprImport_repr___redArg___closed__20);
v___x_670_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__21));
v___x_671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v___x_668_);
v___x_672_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__22));
v___x_673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_669_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set_uint8(v___x_675_, sizeof(void*)*1, v___x_653_);
return v___x_675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleHeader_repr(lean_object* v_x_678_, lean_object* v_prec_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_instReprModuleHeader_repr___redArg(v_x_678_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleHeader_repr___boxed(lean_object* v_x_681_, lean_object* v_prec_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_instReprModuleHeader_repr(v_x_681_, v_prec_682_);
lean_dec(v_prec_682_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0(size_t v_sz_693_, size_t v_i_694_, lean_object* v_bs_695_){
_start:
{
uint8_t v___x_696_; 
v___x_696_ = lean_usize_dec_lt(v_i_694_, v_sz_693_);
if (v___x_696_ == 0)
{
return v_bs_695_;
}
else
{
lean_object* v_v_697_; lean_object* v___x_698_; lean_object* v_bs_x27_699_; lean_object* v___x_700_; size_t v___x_701_; size_t v___x_702_; lean_object* v___x_703_; 
v_v_697_ = lean_array_uget(v_bs_695_, v_i_694_);
v___x_698_ = lean_unsigned_to_nat(0u);
v_bs_x27_699_ = lean_array_uset(v_bs_695_, v_i_694_, v___x_698_);
v___x_700_ = l_Lean_instToJsonImport_toJson(v_v_697_);
v___x_701_ = ((size_t)1ULL);
v___x_702_ = lean_usize_add(v_i_694_, v___x_701_);
v___x_703_ = lean_array_uset(v_bs_x27_699_, v_i_694_, v___x_700_);
v_i_694_ = v___x_702_;
v_bs_695_ = v___x_703_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0___boxed(lean_object* v_sz_705_, lean_object* v_i_706_, lean_object* v_bs_707_){
_start:
{
size_t v_sz_boxed_708_; size_t v_i_boxed_709_; lean_object* v_res_710_; 
v_sz_boxed_708_ = lean_unbox_usize(v_sz_705_);
lean_dec(v_sz_705_);
v_i_boxed_709_ = lean_unbox_usize(v_i_706_);
lean_dec(v_i_706_);
v_res_710_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0(v_sz_boxed_708_, v_i_boxed_709_, v_bs_707_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0(lean_object* v_a_711_){
_start:
{
size_t v_sz_712_; size_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v_sz_712_ = lean_array_size(v_a_711_);
v___x_713_ = ((size_t)0ULL);
v___x_714_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0(v_sz_712_, v___x_713_, v_a_711_);
v___x_715_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonModuleHeader_toJson(lean_object* v_x_716_){
_start:
{
lean_object* v_imports_717_; uint8_t v_isModule_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v_imports_717_ = lean_ctor_get(v_x_716_, 0);
lean_inc_ref(v_imports_717_);
v_isModule_718_ = lean_ctor_get_uint8(v_x_716_, sizeof(void*)*1);
lean_dec_ref(v_x_716_);
v___x_719_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__0));
v___x_720_ = l_Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0(v_imports_717_);
v___x_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = lean_box(0);
v___x_723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__5));
v___x_725_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_725_, 0, v_isModule_718_);
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_724_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v___x_722_);
v___x_728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v___x_722_);
v___x_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_723_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = ((lean_object*)(l_Lean_instToJsonImport_toJson___closed__0));
v___x_731_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(v___x_729_, v___x_730_);
v___x_732_ = l_Lean_Json_mkObj(v___x_731_);
lean_dec(v___x_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1(size_t v_sz_735_, size_t v_i_736_, lean_object* v_bs_737_){
_start:
{
uint8_t v___x_738_; 
v___x_738_ = lean_usize_dec_lt(v_i_736_, v_sz_735_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; 
v___x_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_739_, 0, v_bs_737_);
return v___x_739_;
}
else
{
lean_object* v_v_740_; lean_object* v___x_741_; 
v_v_740_ = lean_array_uget_borrowed(v_bs_737_, v_i_736_);
lean_inc(v_v_740_);
v___x_741_ = l_Lean_instFromJsonImport_fromJson(v_v_740_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec_ref(v_bs_737_);
v_a_742_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_741_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_741_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_751_; lean_object* v_bs_x27_752_; size_t v___x_753_; size_t v___x_754_; lean_object* v___x_755_; 
v_a_750_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_750_);
lean_dec_ref_known(v___x_741_, 1);
v___x_751_ = lean_unsigned_to_nat(0u);
v_bs_x27_752_ = lean_array_uset(v_bs_737_, v_i_736_, v___x_751_);
v___x_753_ = ((size_t)1ULL);
v___x_754_ = lean_usize_add(v_i_736_, v___x_753_);
v___x_755_ = lean_array_uset(v_bs_x27_752_, v_i_736_, v_a_750_);
v_i_736_ = v___x_754_;
v_bs_737_ = v___x_755_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_757_, lean_object* v_i_758_, lean_object* v_bs_759_){
_start:
{
size_t v_sz_boxed_760_; size_t v_i_boxed_761_; lean_object* v_res_762_; 
v_sz_boxed_760_ = lean_unbox_usize(v_sz_757_);
lean_dec(v_sz_757_);
v_i_boxed_761_ = lean_unbox_usize(v_i_758_);
lean_dec(v_i_758_);
v_res_762_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_760_, v_i_boxed_761_, v_bs_759_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0(lean_object* v_x_765_){
_start:
{
if (lean_obj_tag(v_x_765_) == 4)
{
lean_object* v_elems_766_; size_t v_sz_767_; size_t v___x_768_; lean_object* v___x_769_; 
v_elems_766_ = lean_ctor_get(v_x_765_, 0);
lean_inc_ref(v_elems_766_);
lean_dec_ref_known(v_x_765_, 1);
v_sz_767_ = lean_array_size(v_elems_766_);
v___x_768_ = ((size_t)0ULL);
v___x_769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1(v_sz_767_, v___x_768_, v_elems_766_);
return v___x_769_;
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_770_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0));
v___x_771_ = lean_unsigned_to_nat(80u);
v___x_772_ = l_Lean_Json_pretty(v_x_765_, v___x_771_);
v___x_773_ = lean_string_append(v___x_770_, v___x_772_);
lean_dec_ref(v___x_772_);
v___x_774_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_775_ = lean_string_append(v___x_773_, v___x_774_);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
return v___x_776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0(lean_object* v_j_777_, lean_object* v_k_778_){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = l_Lean_Json_getObjValD(v_j_777_, v_k_778_);
v___x_780_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0(v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0___boxed(lean_object* v_j_781_, lean_object* v_k_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0(v_j_781_, v_k_782_);
lean_dec_ref(v_k_782_);
return v_res_783_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__2(void){
_start:
{
uint8_t v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_788_ = 1;
v___x_789_ = ((lean_object*)(l_Lean_instFromJsonModuleHeader_fromJson___closed__1));
v___x_790_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_789_, v___x_788_);
return v___x_790_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__3(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_791_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__4));
v___x_792_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__2, &l_Lean_instFromJsonModuleHeader_fromJson___closed__2_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__2);
v___x_793_ = lean_string_append(v___x_792_, v___x_791_);
return v___x_793_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__5(void){
_start:
{
uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_796_ = 1;
v___x_797_ = ((lean_object*)(l_Lean_instFromJsonModuleHeader_fromJson___closed__4));
v___x_798_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_797_, v___x_796_);
return v___x_798_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__6(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_799_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__5, &l_Lean_instFromJsonModuleHeader_fromJson___closed__5_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__5);
v___x_800_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__3, &l_Lean_instFromJsonModuleHeader_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__3);
v___x_801_ = lean_string_append(v___x_800_, v___x_799_);
return v___x_801_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__7(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_802_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_803_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__6, &l_Lean_instFromJsonModuleHeader_fromJson___closed__6_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__6);
v___x_804_ = lean_string_append(v___x_803_, v___x_802_);
return v___x_804_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__9(void){
_start:
{
uint8_t v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_807_ = 1;
v___x_808_ = ((lean_object*)(l_Lean_instFromJsonModuleHeader_fromJson___closed__8));
v___x_809_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_808_, v___x_807_);
return v___x_809_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__10(void){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_810_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__9, &l_Lean_instFromJsonModuleHeader_fromJson___closed__9_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__9);
v___x_811_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__3, &l_Lean_instFromJsonModuleHeader_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__3);
v___x_812_ = lean_string_append(v___x_811_, v___x_810_);
return v___x_812_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__11(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_813_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_814_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__10, &l_Lean_instFromJsonModuleHeader_fromJson___closed__10_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__10);
v___x_815_ = lean_string_append(v___x_814_, v___x_813_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonModuleHeader_fromJson(lean_object* v_json_816_){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__0));
lean_inc(v_json_816_);
v___x_818_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0(v_json_816_, v___x_817_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_828_; 
lean_dec(v_json_816_);
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_828_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_828_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_828_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_823_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__7, &l_Lean_instFromJsonModuleHeader_fromJson___closed__7_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__7);
v___x_824_ = lean_string_append(v___x_823_, v_a_819_);
lean_dec(v_a_819_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_824_);
v___x_826_ = v___x_821_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
else
{
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_dec(v_json_816_);
v_a_829_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_818_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_818_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set_tag(v___x_831_, 0);
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v_a_837_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_837_);
lean_dec_ref_known(v___x_818_, 1);
v___x_838_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__5));
v___x_839_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(v_json_816_, v___x_838_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_849_; 
lean_dec(v_a_837_);
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_849_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_849_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_849_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_844_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__11, &l_Lean_instFromJsonModuleHeader_fromJson___closed__11_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__11);
v___x_845_ = lean_string_append(v___x_844_, v_a_840_);
lean_dec(v_a_840_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_845_);
v___x_847_ = v___x_842_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
else
{
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec(v_a_837_);
v_a_850_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_839_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_839_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
lean_ctor_set_tag(v___x_852_, 0);
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_867_; 
v_a_858_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_867_ == 0)
{
v___x_860_ = v___x_839_;
v_isShared_861_ = v_isSharedCheck_867_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_839_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_867_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_862_; uint8_t v___x_863_; lean_object* v___x_865_; 
v___x_862_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_862_, 0, v_a_837_);
v___x_863_ = lean_unbox(v_a_858_);
lean_dec(v_a_858_);
lean_ctor_set_uint8(v___x_862_, sizeof(void*)*1, v___x_863_);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v___x_862_);
v___x_865_ = v___x_860_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_862_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0(lean_object* v___y_873_){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_874_ = lean_unsigned_to_nat(0u);
v___x_875_ = ((lean_object*)(l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_876_ = l_String_quote(v___y_873_);
v___x_877_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
v___x_878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_875_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = l_Repr_addAppParen(v___x_878_, v___x_874_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_x_880_, lean_object* v_x_881_, lean_object* v_x_882_){
_start:
{
if (lean_obj_tag(v_x_882_) == 0)
{
lean_dec(v_x_880_);
return v_x_881_;
}
else
{
lean_object* v_head_883_; lean_object* v_tail_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_899_; 
v_head_883_ = lean_ctor_get(v_x_882_, 0);
v_tail_884_ = lean_ctor_get(v_x_882_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v_x_882_);
if (v_isSharedCheck_899_ == 0)
{
v___x_886_ = v_x_882_;
v_isShared_887_ = v_isSharedCheck_899_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_tail_884_);
lean_inc(v_head_883_);
lean_dec(v_x_882_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_899_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
lean_inc(v_x_880_);
if (v_isShared_887_ == 0)
{
lean_ctor_set_tag(v___x_886_, 5);
lean_ctor_set(v___x_886_, 1, v_x_880_);
lean_ctor_set(v___x_886_, 0, v_x_881_);
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_x_881_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_x_880_);
v___x_889_ = v_reuseFailAlloc_898_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_890_ = lean_unsigned_to_nat(0u);
v___x_891_ = ((lean_object*)(l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_892_ = l_String_quote(v_head_883_);
v___x_893_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
v___x_894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_891_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = l_Repr_addAppParen(v___x_894_, v___x_890_);
v___x_896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_889_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v_x_881_ = v___x_896_;
v_x_882_ = v_tail_884_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v_x_902_){
_start:
{
if (lean_obj_tag(v_x_902_) == 0)
{
lean_dec(v_x_900_);
return v_x_901_;
}
else
{
lean_object* v_head_903_; lean_object* v_tail_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_919_; 
v_head_903_ = lean_ctor_get(v_x_902_, 0);
v_tail_904_ = lean_ctor_get(v_x_902_, 1);
v_isSharedCheck_919_ = !lean_is_exclusive(v_x_902_);
if (v_isSharedCheck_919_ == 0)
{
v___x_906_ = v_x_902_;
v_isShared_907_ = v_isSharedCheck_919_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_tail_904_);
lean_inc(v_head_903_);
lean_dec(v_x_902_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_919_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
lean_inc(v_x_900_);
if (v_isShared_907_ == 0)
{
lean_ctor_set_tag(v___x_906_, 5);
lean_ctor_set(v___x_906_, 1, v_x_900_);
lean_ctor_set(v___x_906_, 0, v_x_901_);
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_x_901_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_x_900_);
v___x_909_ = v_reuseFailAlloc_918_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_910_ = lean_unsigned_to_nat(0u);
v___x_911_ = ((lean_object*)(l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_912_ = l_String_quote(v_head_903_);
v___x_913_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
v___x_914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_911_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = l_Repr_addAppParen(v___x_914_, v___x_910_);
v___x_916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_909_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2_spec__4(v_x_900_, v___x_916_, v_tail_904_);
return v___x_917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1(lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
if (lean_obj_tag(v_x_920_) == 0)
{
lean_object* v___x_922_; 
lean_dec(v_x_921_);
v___x_922_ = lean_box(0);
return v___x_922_;
}
else
{
lean_object* v_tail_923_; 
v_tail_923_ = lean_ctor_get(v_x_920_, 1);
if (lean_obj_tag(v_tail_923_) == 0)
{
lean_object* v_head_924_; lean_object* v___x_925_; 
lean_dec(v_x_921_);
v_head_924_ = lean_ctor_get(v_x_920_, 0);
lean_inc(v_head_924_);
lean_dec_ref_known(v_x_920_, 2);
v___x_925_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0(v_head_924_);
return v___x_925_;
}
else
{
lean_object* v_head_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
lean_inc(v_tail_923_);
v_head_926_ = lean_ctor_get(v_x_920_, 0);
lean_inc(v_head_926_);
lean_dec_ref_known(v_x_920_, 2);
v___x_927_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0(v_head_926_);
v___x_928_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2(v_x_921_, v___x_927_, v_tail_923_);
return v___x_928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0(lean_object* v_xs_929_){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; uint8_t v___x_932_; 
v___x_930_ = lean_array_get_size(v_xs_929_);
v___x_931_ = lean_unsigned_to_nat(0u);
v___x_932_ = lean_nat_dec_eq(v___x_930_, v___x_931_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_933_ = lean_array_to_list(v_xs_929_);
v___x_934_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_935_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1(v___x_933_, v___x_934_);
v___x_936_ = lean_obj_once(&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4);
v___x_937_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5));
v___x_938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v___x_935_);
v___x_939_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6));
v___x_940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_938_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_936_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = l_Std_Format_fill(v___x_941_);
return v___x_942_;
}
else
{
lean_object* v___x_943_; 
lean_dec_ref(v_xs_929_);
v___x_943_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8));
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__1_spec__3(lean_object* v_x_944_, lean_object* v_x_945_, lean_object* v_x_946_){
_start:
{
if (lean_obj_tag(v_x_946_) == 0)
{
lean_dec(v_x_944_);
return v_x_945_;
}
else
{
lean_object* v_head_947_; lean_object* v_tail_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_958_; 
v_head_947_ = lean_ctor_get(v_x_946_, 0);
v_tail_948_ = lean_ctor_get(v_x_946_, 1);
v_isSharedCheck_958_ = !lean_is_exclusive(v_x_946_);
if (v_isSharedCheck_958_ == 0)
{
v___x_950_ = v_x_946_;
v_isShared_951_ = v_isSharedCheck_958_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_tail_948_);
lean_inc(v_head_947_);
lean_dec(v_x_946_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_958_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
lean_inc(v_x_944_);
if (v_isShared_951_ == 0)
{
lean_ctor_set_tag(v___x_950_, 5);
lean_ctor_set(v___x_950_, 1, v_x_944_);
lean_ctor_set(v___x_950_, 0, v_x_945_);
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_x_945_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_x_944_);
v___x_953_ = v_reuseFailAlloc_957_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = l_Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0(v_head_947_);
v___x_955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_953_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v_x_945_ = v___x_955_;
v_x_946_ = v_tail_948_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__1(lean_object* v_x_959_, lean_object* v_x_960_){
_start:
{
if (lean_obj_tag(v_x_959_) == 0)
{
lean_object* v___x_961_; 
lean_dec(v_x_960_);
v___x_961_ = lean_box(0);
return v___x_961_;
}
else
{
lean_object* v_tail_962_; 
v_tail_962_ = lean_ctor_get(v_x_959_, 1);
if (lean_obj_tag(v_tail_962_) == 0)
{
lean_object* v_head_963_; lean_object* v___x_964_; 
lean_dec(v_x_960_);
v_head_963_ = lean_ctor_get(v_x_959_, 0);
lean_inc(v_head_963_);
lean_dec_ref_known(v_x_959_, 2);
v___x_964_ = l_Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0(v_head_963_);
return v___x_964_;
}
else
{
lean_object* v_head_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
lean_inc(v_tail_962_);
v_head_965_ = lean_ctor_get(v_x_959_, 0);
lean_inc(v_head_965_);
lean_dec_ref_known(v_x_959_, 2);
v___x_966_ = l_Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0(v_head_965_);
v___x_967_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__1_spec__3(v_x_960_, v___x_966_, v_tail_962_);
return v___x_967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0(lean_object* v_xs_968_){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_969_ = lean_array_get_size(v_xs_968_);
v___x_970_ = lean_unsigned_to_nat(0u);
v___x_971_ = lean_nat_dec_eq(v___x_969_, v___x_970_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_972_ = lean_array_to_list(v_xs_968_);
v___x_973_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_974_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__1(v___x_972_, v___x_973_);
v___x_975_ = lean_obj_once(&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4);
v___x_976_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5));
v___x_977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v___x_974_);
v___x_978_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6));
v___x_979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_977_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_975_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = l_Std_Format_fill(v___x_980_);
return v___x_981_;
}
else
{
lean_object* v___x_982_; 
lean_dec_ref(v_xs_968_);
v___x_982_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8));
return v___x_982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprImportArtifacts_repr___redArg(lean_object* v_x_992_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_993_ = ((lean_object*)(l_Lean_instReprImportArtifacts_repr___redArg___closed__3));
v___x_994_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__7, &l_Lean_instReprModuleHeader_repr___redArg___closed__7_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__7);
v___x_995_ = l_Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0(v_x_992_);
v___x_996_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_994_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = 0;
v___x_998_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set_uint8(v___x_998_, sizeof(void*)*1, v___x_997_);
v___x_999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_993_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__20, &l_Lean_instReprImport_repr___redArg___closed__20_once, _init_l_Lean_instReprImport_repr___redArg___closed__20);
v___x_1001_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__21));
v___x_1002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v___x_999_);
v___x_1003_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__22));
v___x_1004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1000_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set_uint8(v___x_1006_, sizeof(void*)*1, v___x_997_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprImportArtifacts_repr(lean_object* v_x_1007_, lean_object* v_prec_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_instReprImportArtifacts_repr___redArg(v_x_1007_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprImportArtifacts_repr___boxed(lean_object* v_x_1010_, lean_object* v_prec_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_instReprImportArtifacts_repr(v_x_1010_, v_prec_1011_);
lean_dec(v_prec_1011_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonImportArtifacts___lam__0(lean_object* v___x_1019_, lean_object* v_x_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_Array_toJson___redArg(v___x_1019_, v_x_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonImportArtifacts___lam__0(lean_object* v___x_1028_, lean_object* v_x_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_Array_fromJson_x3f___redArg(v___x_1028_, v_x_1029_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
v_a_1039_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1030_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1030_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_olean_x3f(lean_object* v_arts_1053_){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1054_ = lean_unsigned_to_nat(0u);
v___x_1055_ = lean_array_get_size(v_arts_1053_);
v___x_1056_ = lean_nat_dec_lt(v___x_1054_, v___x_1055_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_box(0);
return v___x_1057_;
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; 
v___x_1058_ = lean_array_fget_borrowed(v_arts_1053_, v___x_1054_);
v___x_1059_ = lean_array_get_size(v___x_1058_);
v___x_1060_ = lean_nat_dec_lt(v___x_1054_, v___x_1059_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; 
v___x_1061_ = lean_box(0);
return v___x_1061_;
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_array_fget_borrowed(v___x_1058_, v___x_1054_);
lean_inc(v___x_1062_);
v___x_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_olean_x3f___boxed(lean_object* v_arts_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_ImportArtifacts_olean_x3f(v_arts_1064_);
lean_dec_ref(v_arts_1064_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanServer_x3f(lean_object* v_arts_1066_){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1067_ = lean_unsigned_to_nat(0u);
v___x_1068_ = lean_array_get_size(v_arts_1066_);
v___x_1069_ = lean_nat_dec_lt(v___x_1067_, v___x_1068_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_box(0);
return v___x_1070_;
}
else
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1071_ = lean_array_fget_borrowed(v_arts_1066_, v___x_1067_);
v___x_1072_ = lean_unsigned_to_nat(1u);
v___x_1073_ = lean_array_get_size(v___x_1071_);
v___x_1074_ = lean_nat_dec_lt(v___x_1072_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_box(0);
return v___x_1075_;
}
else
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_array_fget_borrowed(v___x_1071_, v___x_1072_);
lean_inc(v___x_1076_);
v___x_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
return v___x_1077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanServer_x3f___boxed(lean_object* v_arts_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_ImportArtifacts_oleanServer_x3f(v_arts_1078_);
lean_dec_ref(v_arts_1078_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanPrivate_x3f(lean_object* v_arts_1080_){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1081_ = lean_unsigned_to_nat(0u);
v___x_1082_ = lean_array_get_size(v_arts_1080_);
v___x_1083_ = lean_nat_dec_lt(v___x_1081_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_box(0);
return v___x_1084_;
}
else
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1085_ = lean_array_fget_borrowed(v_arts_1080_, v___x_1081_);
v___x_1086_ = lean_unsigned_to_nat(2u);
v___x_1087_ = lean_array_get_size(v___x_1085_);
v___x_1088_ = lean_nat_dec_lt(v___x_1086_, v___x_1087_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_box(0);
return v___x_1089_;
}
else
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_array_fget_borrowed(v___x_1085_, v___x_1086_);
lean_inc(v___x_1090_);
v___x_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
return v___x_1091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanPrivate_x3f___boxed(lean_object* v_arts_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_ImportArtifacts_oleanPrivate_x3f(v_arts_1092_);
lean_dec_ref(v_arts_1092_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_irSig_x3f(lean_object* v_arts_1094_){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1095_ = lean_unsigned_to_nat(1u);
v___x_1096_ = lean_array_get_size(v_arts_1094_);
v___x_1097_ = lean_nat_dec_lt(v___x_1095_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_box(0);
return v___x_1098_;
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1099_ = lean_array_fget_borrowed(v_arts_1094_, v___x_1095_);
v___x_1100_ = lean_unsigned_to_nat(0u);
v___x_1101_ = lean_array_get_size(v___x_1099_);
v___x_1102_ = lean_nat_dec_lt(v___x_1100_, v___x_1101_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_box(0);
return v___x_1103_;
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_array_fget_borrowed(v___x_1099_, v___x_1100_);
lean_inc(v___x_1104_);
v___x_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
return v___x_1105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_irSig_x3f___boxed(lean_object* v_arts_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_ImportArtifacts_irSig_x3f(v_arts_1106_);
lean_dec_ref(v_arts_1106_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_ir_x3f(lean_object* v_arts_1108_){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1109_ = lean_unsigned_to_nat(1u);
v___x_1110_ = lean_array_get_size(v_arts_1108_);
v___x_1111_ = lean_nat_dec_lt(v___x_1109_, v___x_1110_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_box(0);
return v___x_1112_;
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1113_ = lean_array_fget_borrowed(v_arts_1108_, v___x_1109_);
v___x_1114_ = lean_array_get_size(v___x_1113_);
v___x_1115_ = lean_nat_dec_lt(v___x_1109_, v___x_1114_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_box(0);
return v___x_1116_;
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_array_fget_borrowed(v___x_1113_, v___x_1109_);
lean_inc(v___x_1117_);
v___x_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
return v___x_1118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_ir_x3f___boxed(lean_object* v_arts_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_ImportArtifacts_ir_x3f(v_arts_1119_);
lean_dec_ref(v_arts_1119_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanParts(uint8_t v_inServer_1123_, lean_object* v_arts_1124_){
_start:
{
lean_object* v_fnames_1126_; lean_object* v_fnames_1130_; lean_object* v___x_1131_; 
v_fnames_1130_ = ((lean_object*)(l_Lean_ImportArtifacts_oleanParts___closed__0));
v___x_1131_ = l_Lean_ImportArtifacts_olean_x3f(v_arts_1124_);
if (lean_obj_tag(v___x_1131_) == 1)
{
lean_object* v_val_1132_; lean_object* v_fnames_1133_; lean_object* v___x_1134_; 
v_val_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_val_1132_);
lean_dec_ref_known(v___x_1131_, 1);
v_fnames_1133_ = lean_array_push(v_fnames_1130_, v_val_1132_);
v___x_1134_ = l_Lean_ImportArtifacts_oleanServer_x3f(v_arts_1124_);
if (lean_obj_tag(v___x_1134_) == 1)
{
lean_object* v_val_1135_; 
v_val_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_val_1135_);
lean_dec_ref_known(v___x_1134_, 1);
if (v_inServer_1123_ == 0)
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_ImportArtifacts_oleanPrivate_x3f(v_arts_1124_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_dec(v_val_1135_);
v_fnames_1126_ = v_fnames_1133_;
goto v___jp_1125_;
}
else
{
lean_dec_ref_known(v___x_1138_, 1);
goto v___jp_1136_;
}
}
else
{
goto v___jp_1136_;
}
v___jp_1136_:
{
lean_object* v_fnames_1137_; 
v_fnames_1137_ = lean_array_push(v_fnames_1133_, v_val_1135_);
v_fnames_1126_ = v_fnames_1137_;
goto v___jp_1125_;
}
}
else
{
lean_dec(v___x_1134_);
return v_fnames_1133_;
}
}
else
{
lean_dec(v___x_1131_);
return v_fnames_1130_;
}
v___jp_1125_:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_ImportArtifacts_oleanPrivate_x3f(v_arts_1124_);
if (lean_obj_tag(v___x_1127_) == 1)
{
lean_object* v_val_1128_; lean_object* v_fnames_1129_; 
v_val_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_val_1128_);
lean_dec_ref_known(v___x_1127_, 1);
v_fnames_1129_ = lean_array_push(v_fnames_1126_, v_val_1128_);
return v_fnames_1129_;
}
else
{
lean_dec(v___x_1127_);
return v_fnames_1126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanParts___boxed(lean_object* v_inServer_1139_, lean_object* v_arts_1140_){
_start:
{
uint8_t v_inServer_boxed_1141_; lean_object* v_res_1142_; 
v_inServer_boxed_1141_ = lean_unbox(v_inServer_1139_);
v_res_1142_ = l_Lean_ImportArtifacts_oleanParts(v_inServer_boxed_1141_, v_arts_1140_);
lean_dec_ref(v_arts_1140_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_irParts(lean_object* v_arts_1143_){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1144_ = lean_unsigned_to_nat(1u);
v___x_1145_ = lean_array_get_size(v_arts_1143_);
v___x_1146_ = lean_nat_dec_lt(v___x_1144_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; 
v___x_1147_ = ((lean_object*)(l_Lean_ImportArtifacts_oleanParts___closed__0));
return v___x_1147_;
}
else
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_array_fget_borrowed(v_arts_1143_, v___x_1144_);
lean_inc(v___x_1148_);
return v___x_1148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_irParts___boxed(lean_object* v_arts_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_ImportArtifacts_irParts(v_arts_1149_);
lean_dec_ref(v_arts_1149_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(lean_object* v_x_1157_, lean_object* v_x_1158_){
_start:
{
if (lean_obj_tag(v_x_1157_) == 0)
{
lean_object* v___x_1159_; 
v___x_1159_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__1));
return v___x_1159_;
}
else
{
lean_object* v_val_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1175_; 
v_val_1160_ = lean_ctor_get(v_x_1157_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_x_1157_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1162_ = v_x_1157_;
v_isShared_1163_ = v_isSharedCheck_1175_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_val_1160_);
lean_dec(v_x_1157_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1175_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1164_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__3));
v___x_1165_ = lean_unsigned_to_nat(1024u);
v___x_1166_ = ((lean_object*)(l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_1167_ = l_String_quote(v_val_1160_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set_tag(v___x_1162_, 3);
lean_ctor_set(v___x_1162_, 0, v___x_1167_);
v___x_1169_ = v___x_1162_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1166_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = l_Repr_addAppParen(v___x_1170_, v___x_1165_);
v___x_1172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1164_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = l_Repr_addAppParen(v___x_1172_, v_x_1158_);
return v___x_1173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___boxed(lean_object* v_x_1176_, lean_object* v_x_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_x_1176_, v_x_1177_);
lean_dec(v_x_1177_);
return v_res_1178_;
}
}
static lean_object* _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_unsigned_to_nat(9u);
v___x_1189_ = lean_nat_to_int(v___x_1188_);
return v___x_1189_;
}
}
static lean_object* _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_unsigned_to_nat(16u);
v___x_1197_ = lean_nat_to_int(v___x_1196_);
return v___x_1197_;
}
}
static lean_object* _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = lean_unsigned_to_nat(17u);
v___x_1202_ = lean_nat_to_int(v___x_1201_);
return v___x_1202_;
}
}
static lean_object* _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_unsigned_to_nat(7u);
v___x_1213_ = lean_nat_to_int(v___x_1212_);
return v___x_1213_;
}
}
static lean_object* _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_unsigned_to_nat(6u);
v___x_1218_ = lean_nat_to_int(v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleArtifacts_repr___redArg(lean_object* v_x_1222_){
_start:
{
lean_object* v_lean_x3f_1223_; lean_object* v_olean_x3f_1224_; lean_object* v_oleanServer_x3f_1225_; lean_object* v_oleanPrivate_x3f_1226_; lean_object* v_ilean_x3f_1227_; lean_object* v_irSig_x3f_1228_; lean_object* v_ir_x3f_1229_; lean_object* v_c_x3f_1230_; lean_object* v_bc_x3f_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v_lean_x3f_1223_ = lean_ctor_get(v_x_1222_, 0);
lean_inc(v_lean_x3f_1223_);
v_olean_x3f_1224_ = lean_ctor_get(v_x_1222_, 1);
lean_inc(v_olean_x3f_1224_);
v_oleanServer_x3f_1225_ = lean_ctor_get(v_x_1222_, 2);
lean_inc(v_oleanServer_x3f_1225_);
v_oleanPrivate_x3f_1226_ = lean_ctor_get(v_x_1222_, 3);
lean_inc(v_oleanPrivate_x3f_1226_);
v_ilean_x3f_1227_ = lean_ctor_get(v_x_1222_, 4);
lean_inc(v_ilean_x3f_1227_);
v_irSig_x3f_1228_ = lean_ctor_get(v_x_1222_, 5);
lean_inc(v_irSig_x3f_1228_);
v_ir_x3f_1229_ = lean_ctor_get(v_x_1222_, 6);
lean_inc(v_ir_x3f_1229_);
v_c_x3f_1230_ = lean_ctor_get(v_x_1222_, 7);
lean_inc(v_c_x3f_1230_);
v_bc_x3f_1231_ = lean_ctor_get(v_x_1222_, 8);
lean_inc(v_bc_x3f_1231_);
lean_dec_ref(v_x_1222_);
v___x_1232_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__5));
v___x_1233_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__3));
v___x_1234_ = lean_obj_once(&l_Lean_instReprModuleArtifacts_repr___redArg___closed__4, &l_Lean_instReprModuleArtifacts_repr___redArg___closed__4_once, _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__4);
v___x_1235_ = lean_unsigned_to_nat(0u);
v___x_1236_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_lean_x3f_1223_, v___x_1235_);
v___x_1237_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1234_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = 0;
v___x_1239_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
lean_ctor_set_uint8(v___x_1239_, sizeof(void*)*1, v___x_1238_);
v___x_1240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1233_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
v___x_1241_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__9));
v___x_1242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1240_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = lean_box(1);
v___x_1244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1242_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__6));
v___x_1246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1244_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
lean_ctor_set(v___x_1247_, 1, v___x_1232_);
v___x_1248_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__7, &l_Lean_instReprImport_repr___redArg___closed__7_once, _init_l_Lean_instReprImport_repr___redArg___closed__7);
v___x_1249_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_olean_x3f_1224_, v___x_1235_);
v___x_1250_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1248_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
lean_ctor_set_uint8(v___x_1251_, sizeof(void*)*1, v___x_1238_);
v___x_1252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1247_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
lean_ctor_set(v___x_1253_, 1, v___x_1241_);
v___x_1254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
lean_ctor_set(v___x_1254_, 1, v___x_1243_);
v___x_1255_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__8));
v___x_1256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1254_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
lean_ctor_set(v___x_1257_, 1, v___x_1232_);
v___x_1258_ = lean_obj_once(&l_Lean_instReprModuleArtifacts_repr___redArg___closed__9, &l_Lean_instReprModuleArtifacts_repr___redArg___closed__9_once, _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__9);
v___x_1259_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_oleanServer_x3f_1225_, v___x_1235_);
v___x_1260_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1258_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
lean_ctor_set_uint8(v___x_1261_, sizeof(void*)*1, v___x_1238_);
v___x_1262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1257_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
lean_ctor_set(v___x_1263_, 1, v___x_1241_);
v___x_1264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
lean_ctor_set(v___x_1264_, 1, v___x_1243_);
v___x_1265_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__11));
v___x_1266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1264_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
lean_ctor_set(v___x_1267_, 1, v___x_1232_);
v___x_1268_ = lean_obj_once(&l_Lean_instReprModuleArtifacts_repr___redArg___closed__12, &l_Lean_instReprModuleArtifacts_repr___redArg___closed__12_once, _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__12);
v___x_1269_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_oleanPrivate_x3f_1226_, v___x_1235_);
v___x_1270_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1268_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
v___x_1271_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
lean_ctor_set_uint8(v___x_1271_, sizeof(void*)*1, v___x_1238_);
v___x_1272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1267_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
lean_ctor_set(v___x_1273_, 1, v___x_1241_);
v___x_1274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
lean_ctor_set(v___x_1274_, 1, v___x_1243_);
v___x_1275_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__14));
v___x_1276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1274_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v___x_1277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
lean_ctor_set(v___x_1277_, 1, v___x_1232_);
v___x_1278_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_ilean_x3f_1227_, v___x_1235_);
v___x_1279_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1248_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
lean_ctor_set_uint8(v___x_1280_, sizeof(void*)*1, v___x_1238_);
v___x_1281_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1277_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
lean_ctor_set(v___x_1282_, 1, v___x_1241_);
v___x_1283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
lean_ctor_set(v___x_1283_, 1, v___x_1243_);
v___x_1284_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__16));
v___x_1285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1283_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
v___x_1286_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
lean_ctor_set(v___x_1286_, 1, v___x_1232_);
v___x_1287_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_irSig_x3f_1228_, v___x_1235_);
v___x_1288_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1248_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
v___x_1289_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
lean_ctor_set_uint8(v___x_1289_, sizeof(void*)*1, v___x_1238_);
v___x_1290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1286_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v___x_1241_);
v___x_1292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
lean_ctor_set(v___x_1292_, 1, v___x_1243_);
v___x_1293_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__18));
v___x_1294_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1292_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
lean_ctor_set(v___x_1295_, 1, v___x_1232_);
v___x_1296_ = lean_obj_once(&l_Lean_instReprModuleArtifacts_repr___redArg___closed__19, &l_Lean_instReprModuleArtifacts_repr___redArg___closed__19_once, _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__19);
v___x_1297_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_ir_x3f_1229_, v___x_1235_);
v___x_1298_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1296_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
v___x_1299_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set_uint8(v___x_1299_, sizeof(void*)*1, v___x_1238_);
v___x_1300_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1295_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
v___x_1301_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
lean_ctor_set(v___x_1301_, 1, v___x_1241_);
v___x_1302_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v___x_1243_);
v___x_1303_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__21));
v___x_1304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1302_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
v___x_1305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
lean_ctor_set(v___x_1305_, 1, v___x_1232_);
v___x_1306_ = lean_obj_once(&l_Lean_instReprModuleArtifacts_repr___redArg___closed__22, &l_Lean_instReprModuleArtifacts_repr___redArg___closed__22_once, _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__22);
v___x_1307_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_c_x3f_1230_, v___x_1235_);
v___x_1308_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1306_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v___x_1309_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
lean_ctor_set_uint8(v___x_1309_, sizeof(void*)*1, v___x_1238_);
v___x_1310_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1305_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
v___x_1311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set(v___x_1311_, 1, v___x_1241_);
v___x_1312_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
lean_ctor_set(v___x_1312_, 1, v___x_1243_);
v___x_1313_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__24));
v___x_1314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1312_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
v___x_1315_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
lean_ctor_set(v___x_1315_, 1, v___x_1232_);
v___x_1316_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_bc_x3f_1231_, v___x_1235_);
v___x_1317_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1296_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
lean_ctor_set_uint8(v___x_1318_, sizeof(void*)*1, v___x_1238_);
v___x_1319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1315_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
v___x_1320_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__20, &l_Lean_instReprImport_repr___redArg___closed__20_once, _init_l_Lean_instReprImport_repr___redArg___closed__20);
v___x_1321_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__21));
v___x_1322_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
lean_ctor_set(v___x_1322_, 1, v___x_1319_);
v___x_1323_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__22));
v___x_1324_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1322_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
v___x_1325_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1320_);
lean_ctor_set(v___x_1325_, 1, v___x_1324_);
v___x_1326_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
lean_ctor_set_uint8(v___x_1326_, sizeof(void*)*1, v___x_1238_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleArtifacts_repr(lean_object* v_x_1327_, lean_object* v_prec_1328_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_instReprModuleArtifacts_repr___redArg(v_x_1327_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleArtifacts_repr___boxed(lean_object* v_x_1330_, lean_object* v_prec_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_instReprModuleArtifacts_repr(v_x_1330_, v_prec_1331_);
lean_dec(v_prec_1331_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(lean_object* v_k_1339_, lean_object* v_x_1340_){
_start:
{
if (lean_obj_tag(v_x_1340_) == 0)
{
lean_object* v___x_1341_; 
lean_dec_ref(v_k_1339_);
v___x_1341_ = lean_box(0);
return v___x_1341_;
}
else
{
lean_object* v_val_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1352_; 
v_val_1342_ = lean_ctor_get(v_x_1340_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_x_1340_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1344_ = v_x_1340_;
v_isShared_1345_ = v_isSharedCheck_1352_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_val_1342_);
lean_dec(v_x_1340_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1352_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 3);
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_val_1342_);
v___x_1347_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v_k_1339_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = lean_box(0);
v___x_1350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1348_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
return v___x_1350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonModuleArtifacts_toJson(lean_object* v_x_1362_){
_start:
{
lean_object* v_lean_x3f_1363_; lean_object* v_olean_x3f_1364_; lean_object* v_oleanServer_x3f_1365_; lean_object* v_oleanPrivate_x3f_1366_; lean_object* v_ilean_x3f_1367_; lean_object* v_irSig_x3f_1368_; lean_object* v_ir_x3f_1369_; lean_object* v_c_x3f_1370_; lean_object* v_bc_x3f_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v_lean_x3f_1363_ = lean_ctor_get(v_x_1362_, 0);
lean_inc(v_lean_x3f_1363_);
v_olean_x3f_1364_ = lean_ctor_get(v_x_1362_, 1);
lean_inc(v_olean_x3f_1364_);
v_oleanServer_x3f_1365_ = lean_ctor_get(v_x_1362_, 2);
lean_inc(v_oleanServer_x3f_1365_);
v_oleanPrivate_x3f_1366_ = lean_ctor_get(v_x_1362_, 3);
lean_inc(v_oleanPrivate_x3f_1366_);
v_ilean_x3f_1367_ = lean_ctor_get(v_x_1362_, 4);
lean_inc(v_ilean_x3f_1367_);
v_irSig_x3f_1368_ = lean_ctor_get(v_x_1362_, 5);
lean_inc(v_irSig_x3f_1368_);
v_ir_x3f_1369_ = lean_ctor_get(v_x_1362_, 6);
lean_inc(v_ir_x3f_1369_);
v_c_x3f_1370_ = lean_ctor_get(v_x_1362_, 7);
lean_inc(v_c_x3f_1370_);
v_bc_x3f_1371_ = lean_ctor_get(v_x_1362_, 8);
lean_inc(v_bc_x3f_1371_);
lean_dec_ref(v_x_1362_);
v___x_1372_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__0));
v___x_1373_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1372_, v_lean_x3f_1363_);
v___x_1374_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__1));
v___x_1375_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1374_, v_olean_x3f_1364_);
v___x_1376_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__2));
v___x_1377_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1376_, v_oleanServer_x3f_1365_);
v___x_1378_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__3));
v___x_1379_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1378_, v_oleanPrivate_x3f_1366_);
v___x_1380_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__4));
v___x_1381_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1380_, v_ilean_x3f_1367_);
v___x_1382_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__5));
v___x_1383_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1382_, v_irSig_x3f_1368_);
v___x_1384_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__6));
v___x_1385_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1384_, v_ir_x3f_1369_);
v___x_1386_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__7));
v___x_1387_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1386_, v_c_x3f_1370_);
v___x_1388_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__8));
v___x_1389_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1388_, v_bc_x3f_1371_);
v___x_1390_ = lean_box(0);
v___x_1391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1389_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
v___x_1392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1387_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
v___x_1393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1385_);
lean_ctor_set(v___x_1393_, 1, v___x_1392_);
v___x_1394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1383_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v___x_1395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1381_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
v___x_1396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1379_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
v___x_1397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1377_);
lean_ctor_set(v___x_1397_, 1, v___x_1396_);
v___x_1398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1375_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
v___x_1399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1373_);
lean_ctor_set(v___x_1399_, 1, v___x_1398_);
v___x_1400_ = ((lean_object*)(l_Lean_instToJsonImport_toJson___closed__0));
v___x_1401_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(v___x_1399_, v___x_1400_);
v___x_1402_ = l_Lean_Json_mkObj(v___x_1401_);
lean_dec(v___x_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0(lean_object* v_x_1407_){
_start:
{
if (lean_obj_tag(v_x_1407_) == 0)
{
lean_object* v___x_1408_; 
v___x_1408_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0___closed__0));
return v___x_1408_;
}
else
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_Json_getStr_x3f(v_x_1407_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1409_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1409_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
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
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1426_; 
v_a_1418_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1420_ = v___x_1409_;
v_isShared_1421_ = v_isSharedCheck_1426_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1409_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1426_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1422_, 0, v_a_1418_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 0, v___x_1422_);
v___x_1424_ = v___x_1420_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(lean_object* v_j_1427_, lean_object* v_k_1428_){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = l_Lean_Json_getObjValD(v_j_1427_, v_k_1428_);
v___x_1430_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0(v___x_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0___boxed(lean_object* v_j_1431_, lean_object* v_k_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_j_1431_, v_k_1432_);
lean_dec_ref(v_k_1432_);
return v_res_1433_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1438_ = 1;
v___x_1439_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__1));
v___x_1440_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1439_, v___x_1438_);
return v___x_1440_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1441_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__4));
v___x_1442_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2);
v___x_1443_ = lean_string_append(v___x_1442_, v___x_1441_);
return v___x_1443_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1446_ = 1;
v___x_1447_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__4));
v___x_1448_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1447_, v___x_1446_);
return v___x_1448_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1449_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5);
v___x_1450_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1451_ = lean_string_append(v___x_1450_, v___x_1449_);
return v___x_1451_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1452_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1453_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6);
v___x_1454_ = lean_string_append(v___x_1453_, v___x_1452_);
return v___x_1454_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1457_ = 1;
v___x_1458_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__8));
v___x_1459_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1458_, v___x_1457_);
return v___x_1459_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1460_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9);
v___x_1461_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1462_ = lean_string_append(v___x_1461_, v___x_1460_);
return v___x_1462_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1463_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1464_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10);
v___x_1465_ = lean_string_append(v___x_1464_, v___x_1463_);
return v___x_1465_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13(void){
_start:
{
uint8_t v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1468_ = 1;
v___x_1469_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__12));
v___x_1470_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1469_, v___x_1468_);
return v___x_1470_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13);
v___x_1472_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1473_ = lean_string_append(v___x_1472_, v___x_1471_);
return v___x_1473_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1474_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1475_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14);
v___x_1476_ = lean_string_append(v___x_1475_, v___x_1474_);
return v___x_1476_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17(void){
_start:
{
uint8_t v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1479_ = 1;
v___x_1480_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__16));
v___x_1481_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1480_, v___x_1479_);
return v___x_1481_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17);
v___x_1483_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1484_ = lean_string_append(v___x_1483_, v___x_1482_);
return v___x_1484_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1485_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1486_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18);
v___x_1487_ = lean_string_append(v___x_1486_, v___x_1485_);
return v___x_1487_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1490_ = 1;
v___x_1491_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__20));
v___x_1492_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1491_, v___x_1490_);
return v___x_1492_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1493_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21);
v___x_1494_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1495_ = lean_string_append(v___x_1494_, v___x_1493_);
return v___x_1495_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1496_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1497_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22);
v___x_1498_ = lean_string_append(v___x_1497_, v___x_1496_);
return v___x_1498_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25(void){
_start:
{
uint8_t v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1501_ = 1;
v___x_1502_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__24));
v___x_1503_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1502_, v___x_1501_);
return v___x_1503_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26(void){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1504_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25);
v___x_1505_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1506_ = lean_string_append(v___x_1505_, v___x_1504_);
return v___x_1506_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1507_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1508_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26);
v___x_1509_ = lean_string_append(v___x_1508_, v___x_1507_);
return v___x_1509_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29(void){
_start:
{
uint8_t v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1512_ = 1;
v___x_1513_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__28));
v___x_1514_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1513_, v___x_1512_);
return v___x_1514_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1515_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29);
v___x_1516_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1517_ = lean_string_append(v___x_1516_, v___x_1515_);
return v___x_1517_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1518_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1519_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30);
v___x_1520_ = lean_string_append(v___x_1519_, v___x_1518_);
return v___x_1520_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33(void){
_start:
{
uint8_t v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1523_ = 1;
v___x_1524_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__32));
v___x_1525_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1524_, v___x_1523_);
return v___x_1525_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1526_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33);
v___x_1527_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1528_ = lean_string_append(v___x_1527_, v___x_1526_);
return v___x_1528_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1529_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1530_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34);
v___x_1531_ = lean_string_append(v___x_1530_, v___x_1529_);
return v___x_1531_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__37(void){
_start:
{
uint8_t v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1534_ = 1;
v___x_1535_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__36));
v___x_1536_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1535_, v___x_1534_);
return v___x_1536_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__38(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1537_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__37, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__37_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__37);
v___x_1538_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1539_ = lean_string_append(v___x_1538_, v___x_1537_);
return v___x_1539_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__39(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1540_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1541_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__38, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__38_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__38);
v___x_1542_ = lean_string_append(v___x_1541_, v___x_1540_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson(lean_object* v_json_1543_){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__0));
lean_inc(v_json_1543_);
v___x_1545_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1543_, v___x_1544_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1555_; 
lean_dec(v_json_1543_);
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1555_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1555_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1550_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7);
v___x_1551_ = lean_string_append(v___x_1550_, v_a_1546_);
lean_dec(v_a_1546_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v___x_1551_);
v___x_1553_ = v___x_1548_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
else
{
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec(v_json_1543_);
v_a_1556_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1545_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1545_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
lean_ctor_set_tag(v___x_1558_, 0);
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_a_1564_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1565_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__1));
lean_inc(v_json_1543_);
v___x_1566_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1543_, v___x_1565_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1576_; 
lean_dec(v_a_1564_);
lean_dec(v_json_1543_);
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1569_ = v___x_1566_;
v_isShared_1570_ = v_isSharedCheck_1576_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1566_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1576_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1571_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11);
v___x_1572_ = lean_string_append(v___x_1571_, v_a_1567_);
lean_dec(v_a_1567_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v___x_1572_);
v___x_1574_ = v___x_1569_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1572_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
else
{
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec(v_a_1564_);
lean_dec(v_json_1543_);
v_a_1577_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1566_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1566_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set_tag(v___x_1579_, 0);
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v_a_1585_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1566_, 1);
v___x_1586_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__2));
lean_inc(v_json_1543_);
v___x_1587_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1543_, v___x_1586_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1597_; 
lean_dec(v_a_1585_);
lean_dec(v_a_1564_);
lean_dec(v_json_1543_);
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1597_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1597_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1592_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15);
v___x_1593_ = lean_string_append(v___x_1592_, v_a_1588_);
lean_dec(v_a_1588_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1593_);
v___x_1595_ = v___x_1590_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
else
{
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec(v_a_1585_);
lean_dec(v_a_1564_);
lean_dec(v_json_1543_);
v_a_1598_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1587_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1587_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set_tag(v___x_1600_, 0);
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v_a_1606_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1606_);
lean_dec_ref_known(v___x_1587_, 1);
v___x_1607_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__3));
lean_inc(v_json_1543_);
v___x_1608_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1543_, v___x_1607_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1618_; 
lean_dec(v_a_1606_);
lean_dec(v_a_1585_);
lean_dec(v_a_1564_);
lean_dec(v_json_1543_);
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1611_ = v___x_1608_;
v_isShared_1612_ = v_isSharedCheck_1618_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1608_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1618_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1616_; 
v___x_1613_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19);
v___x_1614_ = lean_string_append(v___x_1613_, v_a_1609_);
lean_dec(v_a_1609_);
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 0, v___x_1614_);
v___x_1616_ = v___x_1611_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1614_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
else
{
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec(v_a_1606_);
lean_dec(v_a_1585_);
lean_dec(v_a_1564_);
lean_dec(v_json_1543_);
v_a_1619_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1608_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1608_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
lean_ctor_set_tag(v___x_1621_, 0);
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v_a_1627_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1608_, 1);
v___x_1628_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__4));
lean_inc(v_json_1543_);
v___x_1629_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1543_, v___x_1628_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1639_; 
lean_dec(v_a_1627_);
lean_dec(v_a_1606_);
lean_dec(v_a_1585_);
lean_dec(v_a_1564_);
lean_dec(v_json_1543_);
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1632_ = v___x_1629_;
v_isShared_1633_ = v_isSharedCheck_1639_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1629_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1639_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1637_; 
v___x_1634_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23);
v___x_1635_ = lean_string_append(v___x_1634_, v_a_1630_);
lean_dec(v_a_1630_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v___x_1635_);
v___x_1637_ = v___x_1632_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
else
{
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec(v_a_1627_);
lean_dec(v_a_1606_);
lean_dec(v_a_1585_);
lean_dec(v_a_1564_);
lean_dec(v_json_1543_);
v_a_1640_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1629_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1629_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
lean_ctor_set_tag(v___x_1642_, 0);
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v_a_1648_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1629_, 1);
v___x_1649_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__5));
lean_inc(v_json_1543_);
v___x_1650_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1543_, v___x_1649_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1660_; 
lean_dec(v_a_1648_);
lean_dec(v_a_1627_);
lean_dec(v_a_1606_);
lean_dec(v_a_1585_);
lean_dec(v_a_1564_);
lean_dec(v_json_1543_);
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1653_ = v___x_1650_;
v_isShared_1654_ = v_isSharedCheck_1660_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1650_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1660_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1658_; 
v___x_1655_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27);
v___x_1656_ = lean_string_append(v___x_1655_, v_a_1651_);
lean_dec(v_a_1651_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1656_);
v___x_1658_ = v___x_1653_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1656_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
else
{
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec(v_a_1648_);
lean_dec(v_a_1627_);
lean_dec(v_a_1606_);
lean_dec(v_a_1585_);
lean_dec(v_a_1564_);
lean_dec(v_json_1543_);
v_a_1661_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1650_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1650_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
lean_ctor_set_tag(v___x_1663_, 0);
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v_a_1669_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v___x_1650_, 1);
v___x_1670_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__6));
lean_inc(v_json_1543_);
v___x_1671_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1543_, v___x_1670_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1681_; 
lean_dec(v_a_1669_);
lean_dec(v_a_1648_);
lean_dec(v_a_1627_);
lean_dec(v_a_1606_);
lean_dec(v_a_1585_);
lean_dec(v_a_1564_);
lean_dec(v_json_1543_);
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1674_ = v___x_1671_;
v_isShared_1675_ = v_isSharedCheck_1681_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1671_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1681_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1676_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31);
v___x_1677_ = lean_string_append(v___x_1676_, v_a_1672_);
lean_dec(v_a_1672_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v___x_1677_);
v___x_1679_ = v___x_1674_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
else
{
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec(v_a_1669_);
lean_dec(v_a_1648_);
lean_dec(v_a_1627_);
lean_dec(v_a_1606_);
lean_dec(v_a_1585_);
lean_dec(v_a_1564_);
lean_dec(v_json_1543_);
v_a_1682_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1671_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1671_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
lean_ctor_set_tag(v___x_1684_, 0);
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v_a_1690_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1690_);
lean_dec_ref_known(v___x_1671_, 1);
v___x_1691_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__7));
lean_inc(v_json_1543_);
v___x_1692_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1543_, v___x_1691_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1702_; 
lean_dec(v_a_1690_);
lean_dec(v_a_1669_);
lean_dec(v_a_1648_);
lean_dec(v_a_1627_);
lean_dec(v_a_1606_);
lean_dec(v_a_1585_);
lean_dec(v_a_1564_);
lean_dec(v_json_1543_);
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1695_ = v___x_1692_;
v_isShared_1696_ = v_isSharedCheck_1702_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1692_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1702_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1697_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35);
v___x_1698_ = lean_string_append(v___x_1697_, v_a_1693_);
lean_dec(v_a_1693_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 0, v___x_1698_);
v___x_1700_ = v___x_1695_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
else
{
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec(v_a_1690_);
lean_dec(v_a_1669_);
lean_dec(v_a_1648_);
lean_dec(v_a_1627_);
lean_dec(v_a_1606_);
lean_dec(v_a_1585_);
lean_dec(v_a_1564_);
lean_dec(v_json_1543_);
v_a_1703_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1692_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1692_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
lean_ctor_set_tag(v___x_1705_, 0);
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_a_1711_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1711_);
lean_dec_ref_known(v___x_1692_, 1);
v___x_1712_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__8));
v___x_1713_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1543_, v___x_1712_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1723_; 
lean_dec(v_a_1711_);
lean_dec(v_a_1690_);
lean_dec(v_a_1669_);
lean_dec(v_a_1648_);
lean_dec(v_a_1627_);
lean_dec(v_a_1606_);
lean_dec(v_a_1585_);
lean_dec(v_a_1564_);
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1716_ = v___x_1713_;
v_isShared_1717_ = v_isSharedCheck_1723_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1713_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1723_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1721_; 
v___x_1718_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__39, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__39_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__39);
v___x_1719_ = lean_string_append(v___x_1718_, v_a_1714_);
lean_dec(v_a_1714_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 0, v___x_1719_);
v___x_1721_ = v___x_1716_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
else
{
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec(v_a_1711_);
lean_dec(v_a_1690_);
lean_dec(v_a_1669_);
lean_dec(v_a_1648_);
lean_dec(v_a_1627_);
lean_dec(v_a_1606_);
lean_dec(v_a_1585_);
lean_dec(v_a_1564_);
v_a_1724_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1713_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1713_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set_tag(v___x_1726_, 0);
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1740_; 
v_a_1732_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1734_ = v___x_1713_;
v_isShared_1735_ = v_isSharedCheck_1740_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1713_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1740_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1736_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1736_, 0, v_a_1564_);
lean_ctor_set(v___x_1736_, 1, v_a_1585_);
lean_ctor_set(v___x_1736_, 2, v_a_1606_);
lean_ctor_set(v___x_1736_, 3, v_a_1627_);
lean_ctor_set(v___x_1736_, 4, v_a_1648_);
lean_ctor_set(v___x_1736_, 5, v_a_1669_);
lean_ctor_set(v___x_1736_, 6, v_a_1690_);
lean_ctor_set(v___x_1736_, 7, v_a_1711_);
lean_ctor_set(v___x_1736_, 8, v_a_1732_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v___x_1736_);
v___x_1738_ = v___x_1734_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1736_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
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
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleArtifacts_oleanParts(lean_object* v_arts_1743_){
_start:
{
lean_object* v_olean_x3f_1744_; lean_object* v_oleanServer_x3f_1745_; lean_object* v_oleanPrivate_x3f_1746_; lean_object* v_fnames_1747_; 
v_olean_x3f_1744_ = lean_ctor_get(v_arts_1743_, 1);
lean_inc(v_olean_x3f_1744_);
v_oleanServer_x3f_1745_ = lean_ctor_get(v_arts_1743_, 2);
lean_inc(v_oleanServer_x3f_1745_);
v_oleanPrivate_x3f_1746_ = lean_ctor_get(v_arts_1743_, 3);
lean_inc(v_oleanPrivate_x3f_1746_);
lean_dec_ref(v_arts_1743_);
v_fnames_1747_ = ((lean_object*)(l_Lean_ImportArtifacts_oleanParts___closed__0));
if (lean_obj_tag(v_olean_x3f_1744_) == 1)
{
lean_object* v_val_1748_; lean_object* v_fnames_1749_; 
v_val_1748_ = lean_ctor_get(v_olean_x3f_1744_, 0);
lean_inc(v_val_1748_);
lean_dec_ref_known(v_olean_x3f_1744_, 1);
v_fnames_1749_ = lean_array_push(v_fnames_1747_, v_val_1748_);
if (lean_obj_tag(v_oleanServer_x3f_1745_) == 1)
{
lean_object* v_val_1750_; lean_object* v_fnames_1751_; 
v_val_1750_ = lean_ctor_get(v_oleanServer_x3f_1745_, 0);
lean_inc(v_val_1750_);
lean_dec_ref_known(v_oleanServer_x3f_1745_, 1);
v_fnames_1751_ = lean_array_push(v_fnames_1749_, v_val_1750_);
if (lean_obj_tag(v_oleanPrivate_x3f_1746_) == 1)
{
lean_object* v_val_1752_; lean_object* v_fnames_1753_; 
v_val_1752_ = lean_ctor_get(v_oleanPrivate_x3f_1746_, 0);
lean_inc(v_val_1752_);
lean_dec_ref_known(v_oleanPrivate_x3f_1746_, 1);
v_fnames_1753_ = lean_array_push(v_fnames_1751_, v_val_1752_);
return v_fnames_1753_;
}
else
{
lean_dec(v_oleanPrivate_x3f_1746_);
return v_fnames_1751_;
}
}
else
{
lean_dec(v_oleanPrivate_x3f_1746_);
lean_dec(v_oleanServer_x3f_1745_);
return v_fnames_1749_;
}
}
else
{
lean_dec(v_oleanPrivate_x3f_1746_);
lean_dec(v_oleanServer_x3f_1745_);
lean_dec(v_olean_x3f_1744_);
return v_fnames_1747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleArtifacts_irParts(lean_object* v_arts_1754_){
_start:
{
lean_object* v_irSig_x3f_1755_; lean_object* v_ir_x3f_1756_; lean_object* v_fnames_1757_; 
v_irSig_x3f_1755_ = lean_ctor_get(v_arts_1754_, 5);
lean_inc(v_irSig_x3f_1755_);
v_ir_x3f_1756_ = lean_ctor_get(v_arts_1754_, 6);
lean_inc(v_ir_x3f_1756_);
lean_dec_ref(v_arts_1754_);
v_fnames_1757_ = ((lean_object*)(l_Lean_ImportArtifacts_oleanParts___closed__0));
if (lean_obj_tag(v_irSig_x3f_1755_) == 1)
{
lean_object* v_val_1758_; lean_object* v_fnames_1759_; 
v_val_1758_ = lean_ctor_get(v_irSig_x3f_1755_, 0);
lean_inc(v_val_1758_);
lean_dec_ref_known(v_irSig_x3f_1755_, 1);
v_fnames_1759_ = lean_array_push(v_fnames_1757_, v_val_1758_);
if (lean_obj_tag(v_ir_x3f_1756_) == 1)
{
lean_object* v_val_1760_; lean_object* v_fnames_1761_; 
v_val_1760_ = lean_ctor_get(v_ir_x3f_1756_, 0);
lean_inc(v_val_1760_);
lean_dec_ref_known(v_ir_x3f_1756_, 1);
v_fnames_1761_ = lean_array_push(v_fnames_1759_, v_val_1760_);
return v_fnames_1761_;
}
else
{
lean_dec(v_ir_x3f_1756_);
return v_fnames_1759_;
}
}
else
{
lean_dec(v_ir_x3f_1756_);
lean_dec(v_irSig_x3f_1755_);
return v_fnames_1757_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0(lean_object* v_x_1762_, lean_object* v_x_1763_){
_start:
{
if (lean_obj_tag(v_x_1762_) == 0)
{
lean_object* v___x_1764_; 
v___x_1764_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__1));
return v___x_1764_;
}
else
{
lean_object* v_val_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1776_; 
v_val_1765_ = lean_ctor_get(v_x_1762_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v_x_1762_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1767_ = v_x_1762_;
v_isShared_1768_ = v_isSharedCheck_1776_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_val_1765_);
lean_dec(v_x_1762_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1776_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1772_; 
v___x_1769_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__3));
v___x_1770_ = l_String_quote(v_val_1765_);
if (v_isShared_1768_ == 0)
{
lean_ctor_set_tag(v___x_1767_, 3);
lean_ctor_set(v___x_1767_, 0, v___x_1770_);
v___x_1772_ = v___x_1767_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1769_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
v___x_1774_ = l_Repr_addAppParen(v___x_1773_, v_x_1763_);
return v___x_1774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0___boxed(lean_object* v_x_1777_, lean_object* v_x_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0(v_x_1777_, v_x_1778_);
lean_dec(v_x_1778_);
return v_res_1779_;
}
}
static lean_object* _init_l_Lean_instReprPlugin_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = lean_unsigned_to_nat(8u);
v___x_1790_ = lean_nat_to_int(v___x_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprPlugin_repr___redArg(lean_object* v_x_1794_){
_start:
{
lean_object* v_path_1795_; lean_object* v_initFn_x3f_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1834_; 
v_path_1795_ = lean_ctor_get(v_x_1794_, 0);
v_initFn_x3f_1796_ = lean_ctor_get(v_x_1794_, 1);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_x_1794_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1798_ = v_x_1794_;
v_isShared_1799_ = v_isSharedCheck_1834_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_initFn_x3f_1796_);
lean_inc(v_path_1795_);
lean_dec(v_x_1794_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1834_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1800_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__5));
v___x_1801_ = ((lean_object*)(l_Lean_instReprPlugin_repr___redArg___closed__3));
v___x_1802_ = lean_obj_once(&l_Lean_instReprPlugin_repr___redArg___closed__4, &l_Lean_instReprPlugin_repr___redArg___closed__4_once, _init_l_Lean_instReprPlugin_repr___redArg___closed__4);
v___x_1803_ = lean_unsigned_to_nat(0u);
v___x_1804_ = ((lean_object*)(l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_1805_ = l_String_quote(v_path_1795_);
v___x_1806_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set_tag(v___x_1798_, 5);
lean_ctor_set(v___x_1798_, 1, v___x_1806_);
lean_ctor_set(v___x_1798_, 0, v___x_1804_);
v___x_1808_ = v___x_1798_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1804_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1809_ = l_Repr_addAppParen(v___x_1808_, v___x_1803_);
v___x_1810_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1802_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = 0;
v___x_1812_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1812_, 0, v___x_1810_);
lean_ctor_set_uint8(v___x_1812_, sizeof(void*)*1, v___x_1811_);
v___x_1813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1801_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
v___x_1814_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__9));
v___x_1815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1813_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
v___x_1816_ = lean_box(1);
v___x_1817_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1815_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
v___x_1818_ = ((lean_object*)(l_Lean_instReprPlugin_repr___redArg___closed__6));
v___x_1819_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1817_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v___x_1820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
lean_ctor_set(v___x_1820_, 1, v___x_1800_);
v___x_1821_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__4, &l_Lean_instReprModuleHeader_repr___redArg___closed__4_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__4);
v___x_1822_ = l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0(v_initFn_x3f_1796_, v___x_1803_);
v___x_1823_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1821_);
lean_ctor_set(v___x_1823_, 1, v___x_1822_);
v___x_1824_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
lean_ctor_set_uint8(v___x_1824_, sizeof(void*)*1, v___x_1811_);
v___x_1825_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1820_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__20, &l_Lean_instReprImport_repr___redArg___closed__20_once, _init_l_Lean_instReprImport_repr___redArg___closed__20);
v___x_1827_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__21));
v___x_1828_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
lean_ctor_set(v___x_1828_, 1, v___x_1825_);
v___x_1829_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__22));
v___x_1830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1828_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v___x_1831_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1826_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*1, v___x_1811_);
return v___x_1832_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprPlugin_repr(lean_object* v_x_1835_, lean_object* v_prec_1836_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Lean_instReprPlugin_repr___redArg(v_x_1835_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprPlugin_repr___boxed(lean_object* v_x_1838_, lean_object* v_prec_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Lean_instReprPlugin_repr(v_x_1838_, v_prec_1839_);
lean_dec(v_prec_1839_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonPlugin_toJson_spec__0(lean_object* v_k_1843_, lean_object* v_x_1844_){
_start:
{
if (lean_obj_tag(v_x_1844_) == 0)
{
lean_object* v___x_1845_; 
lean_dec_ref(v_k_1843_);
v___x_1845_ = lean_box(0);
return v___x_1845_;
}
else
{
lean_object* v_val_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1856_; 
v_val_1846_ = lean_ctor_get(v_x_1844_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_x_1844_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1848_ = v_x_1844_;
v_isShared_1849_ = v_isSharedCheck_1856_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_val_1846_);
lean_dec(v_x_1844_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1856_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
lean_ctor_set_tag(v___x_1848_, 3);
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_val_1846_);
v___x_1851_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1852_, 0, v_k_1843_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = lean_box(0);
v___x_1854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1852_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
return v___x_1854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonPlugin_toJson(lean_object* v_x_1858_){
_start:
{
lean_object* v_path_1859_; lean_object* v_initFn_x3f_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1878_; 
v_path_1859_ = lean_ctor_get(v_x_1858_, 0);
v_initFn_x3f_1860_ = lean_ctor_get(v_x_1858_, 1);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_x_1858_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1862_ = v_x_1858_;
v_isShared_1863_ = v_isSharedCheck_1878_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_initFn_x3f_1860_);
lean_inc(v_path_1859_);
lean_dec(v_x_1858_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1878_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1864_ = ((lean_object*)(l_Lean_instReprPlugin_repr___redArg___closed__0));
v___x_1865_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1865_, 0, v_path_1859_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 1, v___x_1865_);
lean_ctor_set(v___x_1862_, 0, v___x_1864_);
v___x_1867_ = v___x_1862_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1864_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1868_ = lean_box(0);
v___x_1869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1867_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = ((lean_object*)(l_Lean_instToJsonPlugin_toJson___closed__0));
v___x_1871_ = l_Lean_Json_opt___at___00Lean_instToJsonPlugin_toJson_spec__0(v___x_1870_, v_initFn_x3f_1860_);
v___x_1872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v___x_1868_);
v___x_1873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1869_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = ((lean_object*)(l_Lean_instToJsonImport_toJson___closed__0));
v___x_1875_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(v___x_1873_, v___x_1874_);
v___x_1876_ = l_Lean_Json_mkObj(v___x_1875_);
lean_dec(v___x_1875_);
return v___x_1876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Plugin_ofFilePath(lean_object* v_path_1881_){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = lean_box(0);
v___x_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1883_, 0, v_path_1881_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__0(lean_object* v_j_1886_, lean_object* v_k_1887_){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = l_Lean_Json_getObjValD(v_j_1886_, v_k_1887_);
v___x_1889_ = l_Lean_Json_getStr_x3f(v___x_1888_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1889_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1889_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
v_a_1898_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1889_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1889_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__0___boxed(lean_object* v_j_1906_, lean_object* v_k_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__0(v_j_1906_, v_k_1907_);
lean_dec_ref(v_k_1907_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1_spec__1(lean_object* v_x_1909_){
_start:
{
if (lean_obj_tag(v_x_1909_) == 0)
{
lean_object* v___x_1910_; 
v___x_1910_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0___closed__0));
return v___x_1910_;
}
else
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_Json_getStr_x3f(v_x_1909_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1911_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1911_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1928_; 
v_a_1920_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1922_ = v___x_1911_;
v_isShared_1923_ = v_isSharedCheck_1928_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1911_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1928_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1924_, 0, v_a_1920_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1924_);
v___x_1926_ = v___x_1922_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1(lean_object* v_j_1929_, lean_object* v_k_1930_){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = l_Lean_Json_getObjValD(v_j_1929_, v_k_1930_);
v___x_1932_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1_spec__1(v___x_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1___boxed(lean_object* v_j_1933_, lean_object* v_k_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1(v_j_1933_, v_k_1934_);
lean_dec_ref(v_k_1934_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Plugin_fromJson_x3f(lean_object* v_data_1939_){
_start:
{
switch(lean_obj_tag(v_data_1939_))
{
case 3:
{
lean_object* v_s_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1948_; 
v_s_1940_ = lean_ctor_get(v_data_1939_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v_data_1939_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1942_ = v_data_1939_;
v_isShared_1943_ = v_isSharedCheck_1948_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_s_1940_);
lean_dec(v_data_1939_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1948_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1944_; lean_object* v___x_1946_; 
v___x_1944_ = l_Lean_Plugin_ofFilePath(v_s_1940_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set_tag(v___x_1942_, 1);
lean_ctor_set(v___x_1942_, 0, v___x_1944_);
v___x_1946_ = v___x_1942_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
case 5:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = ((lean_object*)(l_Lean_instReprPlugin_repr___redArg___closed__0));
lean_inc_ref(v_data_1939_);
v___x_1950_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__0(v_data_1939_, v___x_1949_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_dec_ref_known(v_data_1939_, 1);
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1950_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1950_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v_a_1959_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1959_);
lean_dec_ref_known(v___x_1950_, 1);
v___x_1960_ = ((lean_object*)(l_Lean_instToJsonPlugin_toJson___closed__0));
v___x_1961_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1(v_data_1939_, v___x_1960_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec(v_a_1959_);
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1978_; 
v_a_1970_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1972_ = v___x_1961_;
v_isShared_1973_ = v_isSharedCheck_1978_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1961_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1978_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; lean_object* v___x_1976_; 
v___x_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1974_, 0, v_a_1959_);
lean_ctor_set(v___x_1974_, 1, v_a_1970_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1974_);
v___x_1976_ = v___x_1972_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1974_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
}
default: 
{
lean_object* v___x_1979_; 
lean_dec(v_data_1939_);
v___x_1979_ = ((lean_object*)(l_Lean_Plugin_fromJson_x3f___closed__1));
return v___x_1979_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2_spec__3_spec__5(lean_object* v_x_1982_, lean_object* v_x_1983_, lean_object* v_x_1984_){
_start:
{
if (lean_obj_tag(v_x_1984_) == 0)
{
lean_dec(v_x_1982_);
return v_x_1983_;
}
else
{
lean_object* v_head_1985_; lean_object* v_tail_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1995_; 
v_head_1985_ = lean_ctor_get(v_x_1984_, 0);
v_tail_1986_ = lean_ctor_get(v_x_1984_, 1);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_x_1984_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1988_ = v_x_1984_;
v_isShared_1989_ = v_isSharedCheck_1995_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_tail_1986_);
lean_inc(v_head_1985_);
lean_dec(v_x_1984_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1995_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
lean_inc(v_x_1982_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set_tag(v___x_1988_, 5);
lean_ctor_set(v___x_1988_, 1, v_x_1982_);
lean_ctor_set(v___x_1988_, 0, v_x_1983_);
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_x_1983_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_x_1982_);
v___x_1991_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1992_; 
v___x_1992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
lean_ctor_set(v___x_1992_, 1, v_head_1985_);
v_x_1983_ = v___x_1992_;
v_x_1984_ = v_tail_1986_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2_spec__3(lean_object* v_x_1996_, lean_object* v_x_1997_){
_start:
{
if (lean_obj_tag(v_x_1996_) == 0)
{
lean_object* v___x_1998_; 
lean_dec(v_x_1997_);
v___x_1998_ = lean_box(0);
return v___x_1998_;
}
else
{
lean_object* v_tail_1999_; 
v_tail_1999_ = lean_ctor_get(v_x_1996_, 1);
if (lean_obj_tag(v_tail_1999_) == 0)
{
lean_object* v_head_2000_; 
lean_dec(v_x_1997_);
v_head_2000_ = lean_ctor_get(v_x_1996_, 0);
lean_inc(v_head_2000_);
lean_dec_ref_known(v_x_1996_, 2);
return v_head_2000_;
}
else
{
lean_object* v_head_2001_; lean_object* v___x_2002_; 
lean_inc(v_tail_1999_);
v_head_2001_ = lean_ctor_get(v_x_1996_, 0);
lean_inc(v_head_2001_);
lean_dec_ref_known(v_x_1996_, 2);
v___x_2002_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2_spec__3_spec__5(v_x_1997_, v_head_2001_, v_tail_1999_);
return v___x_2002_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2005_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__0));
v___x_2006_ = lean_string_length(v___x_2005_);
return v___x_2006_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2, &l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2);
v___x_2008_ = lean_nat_to_int(v___x_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(lean_object* v_x_2013_){
_start:
{
lean_object* v_fst_2014_; lean_object* v_snd_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2038_; 
v_fst_2014_ = lean_ctor_get(v_x_2013_, 0);
v_snd_2015_ = lean_ctor_get(v_x_2013_, 1);
v_isSharedCheck_2038_ = !lean_is_exclusive(v_x_2013_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2017_ = v_x_2013_;
v_isShared_2018_ = v_isSharedCheck_2038_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_snd_2015_);
lean_inc(v_fst_2014_);
lean_dec(v_x_2013_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2038_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2019_ = lean_unsigned_to_nat(0u);
v___x_2020_ = l_Lean_Name_reprPrec(v_fst_2014_, v___x_2019_);
v___x_2021_ = lean_box(0);
if (v_isShared_2018_ == 0)
{
lean_ctor_set_tag(v___x_2017_, 1);
lean_ctor_set(v___x_2017_, 1, v___x_2021_);
lean_ctor_set(v___x_2017_, 0, v___x_2020_);
v___x_2023_ = v___x_2017_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; lean_object* v___x_2036_; 
v___x_2024_ = l_Lean_instReprImportArtifacts_repr___redArg(v_snd_2015_);
v___x_2025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
lean_ctor_set(v___x_2025_, 1, v___x_2023_);
v___x_2026_ = l_List_reverse___redArg(v___x_2025_);
v___x_2027_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_2028_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2_spec__3(v___x_2026_, v___x_2027_);
v___x_2029_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3);
v___x_2030_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__4));
v___x_2031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
lean_ctor_set(v___x_2031_, 1, v___x_2028_);
v___x_2032_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__5));
v___x_2033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2031_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v___x_2034_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2029_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
v___x_2035_ = 0;
v___x_2036_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2036_, 0, v___x_2034_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*1, v___x_2035_);
return v___x_2036_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3_spec__5_spec__8(lean_object* v_x_2039_, lean_object* v_x_2040_, lean_object* v_x_2041_){
_start:
{
if (lean_obj_tag(v_x_2041_) == 0)
{
lean_dec(v_x_2039_);
return v_x_2040_;
}
else
{
lean_object* v_head_2042_; lean_object* v_tail_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2053_; 
v_head_2042_ = lean_ctor_get(v_x_2041_, 0);
v_tail_2043_ = lean_ctor_get(v_x_2041_, 1);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_x_2041_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2045_ = v_x_2041_;
v_isShared_2046_ = v_isSharedCheck_2053_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_tail_2043_);
lean_inc(v_head_2042_);
lean_dec(v_x_2041_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2053_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
lean_inc(v_x_2039_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set_tag(v___x_2045_, 5);
lean_ctor_set(v___x_2045_, 1, v_x_2039_);
lean_ctor_set(v___x_2045_, 0, v_x_2040_);
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_x_2040_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_x_2039_);
v___x_2048_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_head_2042_);
v___x_2050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2048_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
v_x_2040_ = v___x_2050_;
v_x_2041_ = v_tail_2043_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3_spec__5(lean_object* v_x_2054_, lean_object* v_x_2055_, lean_object* v_x_2056_){
_start:
{
if (lean_obj_tag(v_x_2056_) == 0)
{
lean_dec(v_x_2054_);
return v_x_2055_;
}
else
{
lean_object* v_head_2057_; lean_object* v_tail_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2068_; 
v_head_2057_ = lean_ctor_get(v_x_2056_, 0);
v_tail_2058_ = lean_ctor_get(v_x_2056_, 1);
v_isSharedCheck_2068_ = !lean_is_exclusive(v_x_2056_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2060_ = v_x_2056_;
v_isShared_2061_ = v_isSharedCheck_2068_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_tail_2058_);
lean_inc(v_head_2057_);
lean_dec(v_x_2056_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2068_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
lean_inc(v_x_2054_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set_tag(v___x_2060_, 5);
lean_ctor_set(v___x_2060_, 1, v_x_2054_);
lean_ctor_set(v___x_2060_, 0, v_x_2055_);
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_x_2055_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_x_2054_);
v___x_2063_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2064_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_head_2057_);
v___x_2065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2063_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3_spec__5_spec__8(v_x_2054_, v___x_2065_, v_tail_2058_);
return v___x_2066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3(lean_object* v_x_2069_, lean_object* v_x_2070_){
_start:
{
if (lean_obj_tag(v_x_2069_) == 0)
{
lean_object* v___x_2071_; 
lean_dec(v_x_2070_);
v___x_2071_ = lean_box(0);
return v___x_2071_;
}
else
{
lean_object* v_tail_2072_; 
v_tail_2072_ = lean_ctor_get(v_x_2069_, 1);
if (lean_obj_tag(v_tail_2072_) == 0)
{
lean_object* v_head_2073_; lean_object* v___x_2074_; 
lean_dec(v_x_2070_);
v_head_2073_ = lean_ctor_get(v_x_2069_, 0);
lean_inc(v_head_2073_);
lean_dec_ref_known(v_x_2069_, 2);
v___x_2074_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_head_2073_);
return v___x_2074_;
}
else
{
lean_object* v_head_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_inc(v_tail_2072_);
v_head_2075_ = lean_ctor_get(v_x_2069_, 0);
lean_inc(v_head_2075_);
lean_dec_ref_known(v_x_2069_, 2);
v___x_2076_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_head_2075_);
v___x_2077_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3_spec__5(v_x_2070_, v___x_2076_, v_tail_2072_);
return v___x_2077_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = ((lean_object*)(l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__2));
v___x_2083_ = lean_string_length(v___x_2082_);
return v___x_2083_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = lean_obj_once(&l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3, &l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3_once, _init_l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3);
v___x_2085_ = lean_nat_to_int(v___x_2084_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg(lean_object* v_a_2088_){
_start:
{
if (lean_obj_tag(v_a_2088_) == 0)
{
lean_object* v___x_2089_; 
v___x_2089_ = ((lean_object*)(l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__1));
return v___x_2089_;
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; lean_object* v___x_2099_; 
v___x_2090_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_2091_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3(v_a_2088_, v___x_2090_);
v___x_2092_ = lean_obj_once(&l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4, &l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4_once, _init_l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4);
v___x_2093_ = ((lean_object*)(l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__5));
v___x_2094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
lean_ctor_set(v___x_2094_, 1, v___x_2091_);
v___x_2095_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6));
v___x_2096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2094_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v___x_2097_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2092_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v___x_2098_ = 0;
v___x_2099_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2099_, 0, v___x_2097_);
lean_ctor_set_uint8(v___x_2099_, sizeof(void*)*1, v___x_2098_);
return v___x_2099_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1(lean_object* v_init_2100_, lean_object* v_x_2101_){
_start:
{
if (lean_obj_tag(v_x_2101_) == 0)
{
lean_object* v_k_2102_; lean_object* v_v_2103_; lean_object* v_l_2104_; lean_object* v_r_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v_k_2102_ = lean_ctor_get(v_x_2101_, 1);
v_v_2103_ = lean_ctor_get(v_x_2101_, 2);
v_l_2104_ = lean_ctor_get(v_x_2101_, 3);
v_r_2105_ = lean_ctor_get(v_x_2101_, 4);
v___x_2106_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1(v_init_2100_, v_r_2105_);
lean_inc(v_v_2103_);
lean_inc(v_k_2102_);
v___x_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2107_, 0, v_k_2102_);
lean_ctor_set(v___x_2107_, 1, v_v_2103_);
v___x_2108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
lean_ctor_set(v___x_2108_, 1, v___x_2106_);
v_init_2100_ = v___x_2108_;
v_x_2101_ = v_l_2104_;
goto _start;
}
else
{
return v_init_2100_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1___boxed(lean_object* v_init_2110_, lean_object* v_x_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1(v_init_2110_, v_x_2111_);
lean_dec(v_x_2111_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5_spec__8_spec__11(lean_object* v_x_2113_, lean_object* v_x_2114_, lean_object* v_x_2115_){
_start:
{
if (lean_obj_tag(v_x_2115_) == 0)
{
lean_dec(v_x_2113_);
return v_x_2114_;
}
else
{
lean_object* v_head_2116_; lean_object* v_tail_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2127_; 
v_head_2116_ = lean_ctor_get(v_x_2115_, 0);
v_tail_2117_ = lean_ctor_get(v_x_2115_, 1);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_x_2115_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2119_ = v_x_2115_;
v_isShared_2120_ = v_isSharedCheck_2127_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_tail_2117_);
lean_inc(v_head_2116_);
lean_dec(v_x_2115_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2127_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
lean_inc(v_x_2113_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set_tag(v___x_2119_, 5);
lean_ctor_set(v___x_2119_, 1, v_x_2113_);
lean_ctor_set(v___x_2119_, 0, v_x_2114_);
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_x_2114_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_x_2113_);
v___x_2122_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = l_Lean_instReprPlugin_repr___redArg(v_head_2116_);
v___x_2124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2122_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v_x_2114_ = v___x_2124_;
v_x_2115_ = v_tail_2117_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5_spec__8(lean_object* v_x_2128_, lean_object* v_x_2129_, lean_object* v_x_2130_){
_start:
{
if (lean_obj_tag(v_x_2130_) == 0)
{
lean_dec(v_x_2128_);
return v_x_2129_;
}
else
{
lean_object* v_head_2131_; lean_object* v_tail_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2142_; 
v_head_2131_ = lean_ctor_get(v_x_2130_, 0);
v_tail_2132_ = lean_ctor_get(v_x_2130_, 1);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_x_2130_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2134_ = v_x_2130_;
v_isShared_2135_ = v_isSharedCheck_2142_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_tail_2132_);
lean_inc(v_head_2131_);
lean_dec(v_x_2130_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2142_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
lean_inc(v_x_2128_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set_tag(v___x_2134_, 5);
lean_ctor_set(v___x_2134_, 1, v_x_2128_);
lean_ctor_set(v___x_2134_, 0, v_x_2129_);
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_x_2129_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_x_2128_);
v___x_2137_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2138_ = l_Lean_instReprPlugin_repr___redArg(v_head_2131_);
v___x_2139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2137_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
v___x_2140_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5_spec__8_spec__11(v_x_2128_, v___x_2139_, v_tail_2132_);
return v___x_2140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5(lean_object* v_x_2143_, lean_object* v_x_2144_){
_start:
{
if (lean_obj_tag(v_x_2143_) == 0)
{
lean_object* v___x_2145_; 
lean_dec(v_x_2144_);
v___x_2145_ = lean_box(0);
return v___x_2145_;
}
else
{
lean_object* v_tail_2146_; 
v_tail_2146_ = lean_ctor_get(v_x_2143_, 1);
if (lean_obj_tag(v_tail_2146_) == 0)
{
lean_object* v_head_2147_; lean_object* v___x_2148_; 
lean_dec(v_x_2144_);
v_head_2147_ = lean_ctor_get(v_x_2143_, 0);
lean_inc(v_head_2147_);
lean_dec_ref_known(v_x_2143_, 2);
v___x_2148_ = l_Lean_instReprPlugin_repr___redArg(v_head_2147_);
return v___x_2148_;
}
else
{
lean_object* v_head_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
lean_inc(v_tail_2146_);
v_head_2149_ = lean_ctor_get(v_x_2143_, 0);
lean_inc(v_head_2149_);
lean_dec_ref_known(v_x_2143_, 2);
v___x_2150_ = l_Lean_instReprPlugin_repr___redArg(v_head_2149_);
v___x_2151_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5_spec__8(v_x_2144_, v___x_2150_, v_tail_2146_);
return v___x_2151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3(lean_object* v_xs_2152_){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; uint8_t v___x_2155_; 
v___x_2153_ = lean_array_get_size(v_xs_2152_);
v___x_2154_ = lean_unsigned_to_nat(0u);
v___x_2155_ = lean_nat_dec_eq(v___x_2153_, v___x_2154_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2156_ = lean_array_to_list(v_xs_2152_);
v___x_2157_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_2158_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5(v___x_2156_, v___x_2157_);
v___x_2159_ = lean_obj_once(&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4);
v___x_2160_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5));
v___x_2161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
lean_ctor_set(v___x_2161_, 1, v___x_2158_);
v___x_2162_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6));
v___x_2163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2161_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2159_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = l_Std_Format_fill(v___x_2164_);
return v___x_2165_;
}
else
{
lean_object* v___x_2166_; 
lean_dec_ref(v_xs_2152_);
v___x_2166_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8));
return v___x_2166_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprModuleSetup_repr_spec__0(lean_object* v_x_2167_, lean_object* v_x_2168_){
_start:
{
if (lean_obj_tag(v_x_2167_) == 0)
{
lean_object* v___x_2169_; 
v___x_2169_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__1));
return v___x_2169_;
}
else
{
lean_object* v_val_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v_val_2170_ = lean_ctor_get(v_x_2167_, 0);
lean_inc(v_val_2170_);
lean_dec_ref_known(v_x_2167_, 1);
v___x_2171_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__3));
v___x_2172_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0(v_val_2170_);
v___x_2173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2171_);
lean_ctor_set(v___x_2173_, 1, v___x_2172_);
v___x_2174_ = l_Repr_addAppParen(v___x_2173_, v_x_2168_);
return v___x_2174_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprModuleSetup_repr_spec__0___boxed(lean_object* v_x_2175_, lean_object* v_x_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Option_repr___at___00Lean_instReprModuleSetup_repr_spec__0(v_x_2175_, v_x_2176_);
lean_dec(v_x_2176_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleSetup_repr___redArg(lean_object* v_x_2208_){
_start:
{
lean_object* v_name_2209_; lean_object* v_package_x3f_2210_; uint8_t v_isModule_2211_; lean_object* v_imports_x3f_2212_; lean_object* v_importArts_2213_; lean_object* v_dynlibs_2214_; lean_object* v_plugins_2215_; lean_object* v_options_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; uint8_t v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v_name_2209_ = lean_ctor_get(v_x_2208_, 0);
lean_inc(v_name_2209_);
v_package_x3f_2210_ = lean_ctor_get(v_x_2208_, 1);
lean_inc(v_package_x3f_2210_);
v_isModule_2211_ = lean_ctor_get_uint8(v_x_2208_, sizeof(void*)*7);
v_imports_x3f_2212_ = lean_ctor_get(v_x_2208_, 2);
lean_inc(v_imports_x3f_2212_);
v_importArts_2213_ = lean_ctor_get(v_x_2208_, 3);
lean_inc(v_importArts_2213_);
v_dynlibs_2214_ = lean_ctor_get(v_x_2208_, 4);
lean_inc_ref(v_dynlibs_2214_);
v_plugins_2215_ = lean_ctor_get(v_x_2208_, 5);
lean_inc_ref(v_plugins_2215_);
v_options_2216_ = lean_ctor_get(v_x_2208_, 6);
lean_inc(v_options_2216_);
lean_dec_ref(v_x_2208_);
v___x_2217_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__5));
v___x_2218_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__3));
v___x_2219_ = lean_obj_once(&l_Lean_instReprPlugin_repr___redArg___closed__4, &l_Lean_instReprPlugin_repr___redArg___closed__4_once, _init_l_Lean_instReprPlugin_repr___redArg___closed__4);
v___x_2220_ = lean_unsigned_to_nat(0u);
v___x_2221_ = l_Lean_Name_reprPrec(v_name_2209_, v___x_2220_);
v___x_2222_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2219_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = 0;
v___x_2224_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2224_, 0, v___x_2222_);
lean_ctor_set_uint8(v___x_2224_, sizeof(void*)*1, v___x_2223_);
v___x_2225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2218_);
lean_ctor_set(v___x_2225_, 1, v___x_2224_);
v___x_2226_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__9));
v___x_2227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2225_);
lean_ctor_set(v___x_2227_, 1, v___x_2226_);
v___x_2228_ = lean_box(1);
v___x_2229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2227_);
lean_ctor_set(v___x_2229_, 1, v___x_2228_);
v___x_2230_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__5));
v___x_2231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2229_);
lean_ctor_set(v___x_2231_, 1, v___x_2230_);
v___x_2232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v___x_2217_);
v___x_2233_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__7, &l_Lean_instReprModuleHeader_repr___redArg___closed__7_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__7);
v___x_2234_ = l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0(v_package_x3f_2210_, v___x_2220_);
v___x_2235_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2233_);
lean_ctor_set(v___x_2235_, 1, v___x_2234_);
v___x_2236_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
lean_ctor_set_uint8(v___x_2236_, sizeof(void*)*1, v___x_2223_);
v___x_2237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2232_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
v___x_2238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
lean_ctor_set(v___x_2238_, 1, v___x_2226_);
v___x_2239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
lean_ctor_set(v___x_2239_, 1, v___x_2228_);
v___x_2240_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__6));
v___x_2241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2239_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
v___x_2242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
lean_ctor_set(v___x_2242_, 1, v___x_2217_);
v___x_2243_ = l_Bool_repr___redArg(v_isModule_2211_);
v___x_2244_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2233_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
lean_ctor_set_uint8(v___x_2245_, sizeof(void*)*1, v___x_2223_);
v___x_2246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2242_);
lean_ctor_set(v___x_2246_, 1, v___x_2245_);
v___x_2247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2246_);
lean_ctor_set(v___x_2247_, 1, v___x_2226_);
v___x_2248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
lean_ctor_set(v___x_2248_, 1, v___x_2228_);
v___x_2249_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__7));
v___x_2250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2248_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
v___x_2251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
lean_ctor_set(v___x_2251_, 1, v___x_2217_);
v___x_2252_ = l_Option_repr___at___00Lean_instReprModuleSetup_repr_spec__0(v_imports_x3f_2212_, v___x_2220_);
v___x_2253_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2233_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
v___x_2254_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
lean_ctor_set_uint8(v___x_2254_, sizeof(void*)*1, v___x_2223_);
v___x_2255_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2251_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
v___x_2256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
lean_ctor_set(v___x_2256_, 1, v___x_2226_);
v___x_2257_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
lean_ctor_set(v___x_2257_, 1, v___x_2228_);
v___x_2258_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__9));
v___x_2259_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2257_);
lean_ctor_set(v___x_2259_, 1, v___x_2258_);
v___x_2260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
lean_ctor_set(v___x_2260_, 1, v___x_2217_);
v___x_2261_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__15, &l_Lean_instReprImport_repr___redArg___closed__15_once, _init_l_Lean_instReprImport_repr___redArg___closed__15);
v___x_2262_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__11));
v___x_2263_ = lean_box(0);
v___x_2264_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1(v___x_2263_, v_importArts_2213_);
lean_dec(v_importArts_2213_);
v___x_2265_ = l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg(v___x_2264_);
v___x_2266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2262_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
v___x_2267_ = l_Repr_addAppParen(v___x_2266_, v___x_2220_);
v___x_2268_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2261_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
v___x_2269_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
lean_ctor_set_uint8(v___x_2269_, sizeof(void*)*1, v___x_2223_);
v___x_2270_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2260_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
v___x_2271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
lean_ctor_set(v___x_2271_, 1, v___x_2226_);
v___x_2272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
lean_ctor_set(v___x_2272_, 1, v___x_2228_);
v___x_2273_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__13));
v___x_2274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2272_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
v___x_2275_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
lean_ctor_set(v___x_2275_, 1, v___x_2217_);
v___x_2276_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__4, &l_Lean_instReprModuleHeader_repr___redArg___closed__4_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__4);
v___x_2277_ = l_Array_repr___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0(v_dynlibs_2214_);
v___x_2278_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2276_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
lean_ctor_set_uint8(v___x_2279_, sizeof(void*)*1, v___x_2223_);
v___x_2280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2275_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
v___x_2281_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
lean_ctor_set(v___x_2281_, 1, v___x_2226_);
v___x_2282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
lean_ctor_set(v___x_2282_, 1, v___x_2228_);
v___x_2283_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__15));
v___x_2284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2282_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
v___x_2285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
lean_ctor_set(v___x_2285_, 1, v___x_2217_);
v___x_2286_ = l_Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3(v_plugins_2215_);
v___x_2287_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2276_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
v___x_2288_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
lean_ctor_set_uint8(v___x_2288_, sizeof(void*)*1, v___x_2223_);
v___x_2289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2285_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
v___x_2290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
lean_ctor_set(v___x_2290_, 1, v___x_2226_);
v___x_2291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
lean_ctor_set(v___x_2291_, 1, v___x_2228_);
v___x_2292_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__17));
v___x_2293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2291_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
lean_ctor_set(v___x_2294_, 1, v___x_2217_);
v___x_2295_ = l_Lean_instReprLeanOptions_repr___redArg(v_options_2216_);
lean_dec(v_options_2216_);
v___x_2296_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2276_);
lean_ctor_set(v___x_2296_, 1, v___x_2295_);
v___x_2297_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
lean_ctor_set_uint8(v___x_2297_, sizeof(void*)*1, v___x_2223_);
v___x_2298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2294_);
lean_ctor_set(v___x_2298_, 1, v___x_2297_);
v___x_2299_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__20, &l_Lean_instReprImport_repr___redArg___closed__20_once, _init_l_Lean_instReprImport_repr___redArg___closed__20);
v___x_2300_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__21));
v___x_2301_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
lean_ctor_set(v___x_2301_, 1, v___x_2298_);
v___x_2302_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__22));
v___x_2303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2301_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2299_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
v___x_2305_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
lean_ctor_set_uint8(v___x_2305_, sizeof(void*)*1, v___x_2223_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleSetup_repr(lean_object* v_x_2306_, lean_object* v_prec_2307_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_instReprModuleSetup_repr___redArg(v_x_2306_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleSetup_repr___boxed(lean_object* v_x_2309_, lean_object* v_prec_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Lean_instReprModuleSetup_repr(v_x_2309_, v_prec_2310_);
lean_dec(v_prec_2310_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2(lean_object* v_a_2312_, lean_object* v_n_2313_){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg(v_a_2312_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___boxed(lean_object* v_a_2315_, lean_object* v_n_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2(v_a_2315_, v_n_2316_);
lean_dec(v_n_2316_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2(lean_object* v_x_2318_, lean_object* v_x_2319_){
_start:
{
lean_object* v___x_2320_; 
v___x_2320_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_x_2318_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___boxed(lean_object* v_x_2321_, lean_object* v_x_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2(v_x_2321_, v_x_2322_);
lean_dec(v_x_2322_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__5(size_t v_sz_2334_, size_t v_i_2335_, lean_object* v_bs_2336_){
_start:
{
uint8_t v___x_2337_; 
v___x_2337_ = lean_usize_dec_lt(v_i_2335_, v_sz_2334_);
if (v___x_2337_ == 0)
{
return v_bs_2336_;
}
else
{
lean_object* v_v_2338_; lean_object* v___x_2339_; lean_object* v_bs_x27_2340_; lean_object* v___x_2341_; size_t v___x_2342_; size_t v___x_2343_; lean_object* v___x_2344_; 
v_v_2338_ = lean_array_uget(v_bs_2336_, v_i_2335_);
v___x_2339_ = lean_unsigned_to_nat(0u);
v_bs_x27_2340_ = lean_array_uset(v_bs_2336_, v_i_2335_, v___x_2339_);
v___x_2341_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2341_, 0, v_v_2338_);
v___x_2342_ = ((size_t)1ULL);
v___x_2343_ = lean_usize_add(v_i_2335_, v___x_2342_);
v___x_2344_ = lean_array_uset(v_bs_x27_2340_, v_i_2335_, v___x_2341_);
v_i_2335_ = v___x_2343_;
v_bs_2336_ = v___x_2344_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__5___boxed(lean_object* v_sz_2346_, lean_object* v_i_2347_, lean_object* v_bs_2348_){
_start:
{
size_t v_sz_boxed_2349_; size_t v_i_boxed_2350_; lean_object* v_res_2351_; 
v_sz_boxed_2349_ = lean_unbox_usize(v_sz_2346_);
lean_dec(v_sz_2346_);
v_i_boxed_2350_ = lean_unbox_usize(v_i_2347_);
lean_dec(v_i_2347_);
v_res_2351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__5(v_sz_boxed_2349_, v_i_boxed_2350_, v_bs_2348_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2(lean_object* v_a_2352_){
_start:
{
size_t v_sz_2353_; size_t v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v_sz_2353_ = lean_array_size(v_a_2352_);
v___x_2354_ = ((size_t)0ULL);
v___x_2355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__5(v_sz_2353_, v___x_2354_, v_a_2352_);
v___x_2356_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2(size_t v_sz_2357_, size_t v_i_2358_, lean_object* v_bs_2359_){
_start:
{
uint8_t v___x_2360_; 
v___x_2360_ = lean_usize_dec_lt(v_i_2358_, v_sz_2357_);
if (v___x_2360_ == 0)
{
return v_bs_2359_;
}
else
{
lean_object* v_v_2361_; lean_object* v___x_2362_; lean_object* v_bs_x27_2363_; lean_object* v___x_2364_; size_t v___x_2365_; size_t v___x_2366_; lean_object* v___x_2367_; 
v_v_2361_ = lean_array_uget(v_bs_2359_, v_i_2358_);
v___x_2362_ = lean_unsigned_to_nat(0u);
v_bs_x27_2363_ = lean_array_uset(v_bs_2359_, v_i_2358_, v___x_2362_);
v___x_2364_ = l_Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2(v_v_2361_);
v___x_2365_ = ((size_t)1ULL);
v___x_2366_ = lean_usize_add(v_i_2358_, v___x_2365_);
v___x_2367_ = lean_array_uset(v_bs_x27_2363_, v_i_2358_, v___x_2364_);
v_i_2358_ = v___x_2366_;
v_bs_2359_ = v___x_2367_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_2369_, lean_object* v_i_2370_, lean_object* v_bs_2371_){
_start:
{
size_t v_sz_boxed_2372_; size_t v_i_boxed_2373_; lean_object* v_res_2374_; 
v_sz_boxed_2372_ = lean_unbox_usize(v_sz_2369_);
lean_dec(v_sz_2369_);
v_i_boxed_2373_ = lean_unbox_usize(v_i_2370_);
lean_dec(v_i_2370_);
v_res_2374_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2(v_sz_boxed_2372_, v_i_boxed_2373_, v_bs_2371_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1(lean_object* v_a_2375_){
_start:
{
size_t v_sz_2376_; size_t v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v_sz_2376_ = lean_array_size(v_a_2375_);
v___x_2377_ = ((size_t)0ULL);
v___x_2378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2(v_sz_2376_, v___x_2377_, v_a_2375_);
v___x_2379_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4___redArg(lean_object* v_msg_2380_){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = lean_box(1);
v___x_2382_ = lean_panic_fn_borrowed(v___x_2381_, v_msg_2380_);
return v___x_2382_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2386_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__2));
v___x_2387_ = lean_unsigned_to_nat(35u);
v___x_2388_ = lean_unsigned_to_nat(182u);
v___x_2389_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__1));
v___x_2390_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__0));
v___x_2391_ = l_mkPanicMessageWithDecl(v___x_2390_, v___x_2389_, v___x_2388_, v___x_2387_, v___x_2386_);
return v___x_2391_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2392_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__2));
v___x_2393_ = lean_unsigned_to_nat(21u);
v___x_2394_ = lean_unsigned_to_nat(183u);
v___x_2395_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__1));
v___x_2396_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__0));
v___x_2397_ = l_mkPanicMessageWithDecl(v___x_2396_, v___x_2395_, v___x_2394_, v___x_2393_, v___x_2392_);
return v___x_2397_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2400_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__6));
v___x_2401_ = lean_unsigned_to_nat(35u);
v___x_2402_ = lean_unsigned_to_nat(276u);
v___x_2403_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__5));
v___x_2404_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__0));
v___x_2405_ = l_mkPanicMessageWithDecl(v___x_2404_, v___x_2403_, v___x_2402_, v___x_2401_, v___x_2400_);
return v___x_2405_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2406_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__6));
v___x_2407_ = lean_unsigned_to_nat(21u);
v___x_2408_ = lean_unsigned_to_nat(277u);
v___x_2409_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__5));
v___x_2410_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__0));
v___x_2411_ = l_mkPanicMessageWithDecl(v___x_2410_, v___x_2409_, v___x_2408_, v___x_2407_, v___x_2406_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg(lean_object* v_k_2412_, lean_object* v_v_2413_, lean_object* v_t_2414_){
_start:
{
if (lean_obj_tag(v_t_2414_) == 0)
{
lean_object* v_size_2415_; lean_object* v_k_2416_; lean_object* v_v_2417_; lean_object* v_l_2418_; lean_object* v_r_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2775_; 
v_size_2415_ = lean_ctor_get(v_t_2414_, 0);
v_k_2416_ = lean_ctor_get(v_t_2414_, 1);
v_v_2417_ = lean_ctor_get(v_t_2414_, 2);
v_l_2418_ = lean_ctor_get(v_t_2414_, 3);
v_r_2419_ = lean_ctor_get(v_t_2414_, 4);
v_isSharedCheck_2775_ = !lean_is_exclusive(v_t_2414_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2421_ = v_t_2414_;
v_isShared_2422_ = v_isSharedCheck_2775_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_r_2419_);
lean_inc(v_l_2418_);
lean_inc(v_v_2417_);
lean_inc(v_k_2416_);
lean_inc(v_size_2415_);
lean_dec(v_t_2414_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2775_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
uint8_t v___x_2423_; 
v___x_2423_ = lean_string_compare(v_k_2412_, v_k_2416_);
switch(v___x_2423_)
{
case 0:
{
lean_object* v___x_2424_; 
lean_dec(v_size_2415_);
v___x_2424_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg(v_k_2412_, v_v_2413_, v_l_2418_);
if (lean_obj_tag(v_r_2419_) == 0)
{
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_size_2425_; lean_object* v_size_2426_; lean_object* v_k_2427_; lean_object* v_v_2428_; lean_object* v_l_2429_; lean_object* v_r_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; 
v_size_2425_ = lean_ctor_get(v_r_2419_, 0);
v_size_2426_ = lean_ctor_get(v___x_2424_, 0);
v_k_2427_ = lean_ctor_get(v___x_2424_, 1);
v_v_2428_ = lean_ctor_get(v___x_2424_, 2);
v_l_2429_ = lean_ctor_get(v___x_2424_, 3);
v_r_2430_ = lean_ctor_get(v___x_2424_, 4);
lean_inc(v_r_2430_);
v___x_2431_ = lean_unsigned_to_nat(3u);
v___x_2432_ = lean_nat_mul(v___x_2431_, v_size_2425_);
v___x_2433_ = lean_nat_dec_lt(v___x_2432_, v_size_2426_);
lean_dec(v___x_2432_);
if (v___x_2433_ == 0)
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2438_; 
lean_dec(v_r_2430_);
v___x_2434_ = lean_unsigned_to_nat(1u);
v___x_2435_ = lean_nat_add(v___x_2434_, v_size_2426_);
v___x_2436_ = lean_nat_add(v___x_2435_, v_size_2425_);
lean_dec(v___x_2435_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 3, v___x_2424_);
lean_ctor_set(v___x_2421_, 0, v___x_2436_);
v___x_2438_ = v___x_2421_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2436_);
lean_ctor_set(v_reuseFailAlloc_2439_, 1, v_k_2416_);
lean_ctor_set(v_reuseFailAlloc_2439_, 2, v_v_2417_);
lean_ctor_set(v_reuseFailAlloc_2439_, 3, v___x_2424_);
lean_ctor_set(v_reuseFailAlloc_2439_, 4, v_r_2419_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
else
{
lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2511_; 
lean_inc(v_l_2429_);
lean_inc(v_v_2428_);
lean_inc(v_k_2427_);
lean_inc(v_size_2426_);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2511_ == 0)
{
lean_object* v_unused_2512_; lean_object* v_unused_2513_; lean_object* v_unused_2514_; lean_object* v_unused_2515_; lean_object* v_unused_2516_; 
v_unused_2512_ = lean_ctor_get(v___x_2424_, 4);
lean_dec(v_unused_2512_);
v_unused_2513_ = lean_ctor_get(v___x_2424_, 3);
lean_dec(v_unused_2513_);
v_unused_2514_ = lean_ctor_get(v___x_2424_, 2);
lean_dec(v_unused_2514_);
v_unused_2515_ = lean_ctor_get(v___x_2424_, 1);
lean_dec(v_unused_2515_);
v_unused_2516_ = lean_ctor_get(v___x_2424_, 0);
lean_dec(v_unused_2516_);
v___x_2441_ = v___x_2424_;
v_isShared_2442_ = v_isSharedCheck_2511_;
goto v_resetjp_2440_;
}
else
{
lean_dec(v___x_2424_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2511_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
if (lean_obj_tag(v_l_2429_) == 0)
{
if (lean_obj_tag(v_r_2430_) == 0)
{
lean_object* v_size_2443_; lean_object* v_size_2444_; lean_object* v_k_2445_; lean_object* v_v_2446_; lean_object* v_l_2447_; lean_object* v_r_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; uint8_t v___x_2451_; 
v_size_2443_ = lean_ctor_get(v_l_2429_, 0);
v_size_2444_ = lean_ctor_get(v_r_2430_, 0);
v_k_2445_ = lean_ctor_get(v_r_2430_, 1);
v_v_2446_ = lean_ctor_get(v_r_2430_, 2);
v_l_2447_ = lean_ctor_get(v_r_2430_, 3);
v_r_2448_ = lean_ctor_get(v_r_2430_, 4);
v___x_2449_ = lean_unsigned_to_nat(2u);
v___x_2450_ = lean_nat_mul(v___x_2449_, v_size_2443_);
v___x_2451_ = lean_nat_dec_lt(v_size_2444_, v___x_2450_);
lean_dec(v___x_2450_);
if (v___x_2451_ == 0)
{
lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2481_; 
lean_inc(v_r_2448_);
lean_inc(v_l_2447_);
lean_inc(v_v_2446_);
lean_inc(v_k_2445_);
v_isSharedCheck_2481_ = !lean_is_exclusive(v_r_2430_);
if (v_isSharedCheck_2481_ == 0)
{
lean_object* v_unused_2482_; lean_object* v_unused_2483_; lean_object* v_unused_2484_; lean_object* v_unused_2485_; lean_object* v_unused_2486_; 
v_unused_2482_ = lean_ctor_get(v_r_2430_, 4);
lean_dec(v_unused_2482_);
v_unused_2483_ = lean_ctor_get(v_r_2430_, 3);
lean_dec(v_unused_2483_);
v_unused_2484_ = lean_ctor_get(v_r_2430_, 2);
lean_dec(v_unused_2484_);
v_unused_2485_ = lean_ctor_get(v_r_2430_, 1);
lean_dec(v_unused_2485_);
v_unused_2486_ = lean_ctor_get(v_r_2430_, 0);
lean_dec(v_unused_2486_);
v___x_2453_ = v_r_2430_;
v_isShared_2454_ = v_isSharedCheck_2481_;
goto v_resetjp_2452_;
}
else
{
lean_dec(v_r_2430_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2481_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___x_2469_; lean_object* v___y_2471_; 
v___x_2455_ = lean_unsigned_to_nat(1u);
v___x_2456_ = lean_nat_add(v___x_2455_, v_size_2426_);
lean_dec(v_size_2426_);
v___x_2457_ = lean_nat_add(v___x_2456_, v_size_2425_);
lean_dec(v___x_2456_);
v___x_2469_ = lean_nat_add(v___x_2455_, v_size_2443_);
if (lean_obj_tag(v_l_2447_) == 0)
{
lean_object* v_size_2479_; 
v_size_2479_ = lean_ctor_get(v_l_2447_, 0);
lean_inc(v_size_2479_);
v___y_2471_ = v_size_2479_;
goto v___jp_2470_;
}
else
{
lean_object* v___x_2480_; 
v___x_2480_ = lean_unsigned_to_nat(0u);
v___y_2471_ = v___x_2480_;
goto v___jp_2470_;
}
v___jp_2458_:
{
lean_object* v___x_2462_; lean_object* v___x_2464_; 
v___x_2462_ = lean_nat_add(v___y_2460_, v___y_2461_);
lean_dec(v___y_2461_);
lean_dec(v___y_2460_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 4, v_r_2419_);
lean_ctor_set(v___x_2453_, 3, v_r_2448_);
lean_ctor_set(v___x_2453_, 2, v_v_2417_);
lean_ctor_set(v___x_2453_, 1, v_k_2416_);
lean_ctor_set(v___x_2453_, 0, v___x_2462_);
v___x_2464_ = v___x_2453_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_k_2416_);
lean_ctor_set(v_reuseFailAlloc_2468_, 2, v_v_2417_);
lean_ctor_set(v_reuseFailAlloc_2468_, 3, v_r_2448_);
lean_ctor_set(v_reuseFailAlloc_2468_, 4, v_r_2419_);
v___x_2464_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
lean_object* v___x_2466_; 
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 4, v___x_2464_);
lean_ctor_set(v___x_2441_, 3, v___y_2459_);
lean_ctor_set(v___x_2441_, 2, v_v_2446_);
lean_ctor_set(v___x_2441_, 1, v_k_2445_);
lean_ctor_set(v___x_2441_, 0, v___x_2457_);
v___x_2466_ = v___x_2441_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2457_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_k_2445_);
lean_ctor_set(v_reuseFailAlloc_2467_, 2, v_v_2446_);
lean_ctor_set(v_reuseFailAlloc_2467_, 3, v___y_2459_);
lean_ctor_set(v_reuseFailAlloc_2467_, 4, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
v___jp_2470_:
{
lean_object* v___x_2472_; lean_object* v___x_2474_; 
v___x_2472_ = lean_nat_add(v___x_2469_, v___y_2471_);
lean_dec(v___y_2471_);
lean_dec(v___x_2469_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v_l_2447_);
lean_ctor_set(v___x_2421_, 3, v_l_2429_);
lean_ctor_set(v___x_2421_, 2, v_v_2428_);
lean_ctor_set(v___x_2421_, 1, v_k_2427_);
lean_ctor_set(v___x_2421_, 0, v___x_2472_);
v___x_2474_ = v___x_2421_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2472_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_k_2427_);
lean_ctor_set(v_reuseFailAlloc_2478_, 2, v_v_2428_);
lean_ctor_set(v_reuseFailAlloc_2478_, 3, v_l_2429_);
lean_ctor_set(v_reuseFailAlloc_2478_, 4, v_l_2447_);
v___x_2474_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
lean_object* v___x_2475_; 
v___x_2475_ = lean_nat_add(v___x_2455_, v_size_2425_);
if (lean_obj_tag(v_r_2448_) == 0)
{
lean_object* v_size_2476_; 
v_size_2476_ = lean_ctor_get(v_r_2448_, 0);
lean_inc(v_size_2476_);
v___y_2459_ = v___x_2474_;
v___y_2460_ = v___x_2475_;
v___y_2461_ = v_size_2476_;
goto v___jp_2458_;
}
else
{
lean_object* v___x_2477_; 
v___x_2477_ = lean_unsigned_to_nat(0u);
v___y_2459_ = v___x_2474_;
v___y_2460_ = v___x_2475_;
v___y_2461_ = v___x_2477_;
goto v___jp_2458_;
}
}
}
}
}
else
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2493_; 
lean_del_object(v___x_2421_);
v___x_2487_ = lean_unsigned_to_nat(1u);
v___x_2488_ = lean_nat_add(v___x_2487_, v_size_2426_);
lean_dec(v_size_2426_);
v___x_2489_ = lean_nat_add(v___x_2488_, v_size_2425_);
lean_dec(v___x_2488_);
v___x_2490_ = lean_nat_add(v___x_2487_, v_size_2425_);
v___x_2491_ = lean_nat_add(v___x_2490_, v_size_2444_);
lean_dec(v___x_2490_);
lean_inc_ref(v_r_2419_);
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 4, v_r_2419_);
lean_ctor_set(v___x_2441_, 3, v_r_2430_);
lean_ctor_set(v___x_2441_, 2, v_v_2417_);
lean_ctor_set(v___x_2441_, 1, v_k_2416_);
lean_ctor_set(v___x_2441_, 0, v___x_2491_);
v___x_2493_ = v___x_2441_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2491_);
lean_ctor_set(v_reuseFailAlloc_2506_, 1, v_k_2416_);
lean_ctor_set(v_reuseFailAlloc_2506_, 2, v_v_2417_);
lean_ctor_set(v_reuseFailAlloc_2506_, 3, v_r_2430_);
lean_ctor_set(v_reuseFailAlloc_2506_, 4, v_r_2419_);
v___x_2493_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
v_isSharedCheck_2500_ = !lean_is_exclusive(v_r_2419_);
if (v_isSharedCheck_2500_ == 0)
{
lean_object* v_unused_2501_; lean_object* v_unused_2502_; lean_object* v_unused_2503_; lean_object* v_unused_2504_; lean_object* v_unused_2505_; 
v_unused_2501_ = lean_ctor_get(v_r_2419_, 4);
lean_dec(v_unused_2501_);
v_unused_2502_ = lean_ctor_get(v_r_2419_, 3);
lean_dec(v_unused_2502_);
v_unused_2503_ = lean_ctor_get(v_r_2419_, 2);
lean_dec(v_unused_2503_);
v_unused_2504_ = lean_ctor_get(v_r_2419_, 1);
lean_dec(v_unused_2504_);
v_unused_2505_ = lean_ctor_get(v_r_2419_, 0);
lean_dec(v_unused_2505_);
v___x_2495_ = v_r_2419_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_dec(v_r_2419_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 4, v___x_2493_);
lean_ctor_set(v___x_2495_, 3, v_l_2429_);
lean_ctor_set(v___x_2495_, 2, v_v_2428_);
lean_ctor_set(v___x_2495_, 1, v_k_2427_);
lean_ctor_set(v___x_2495_, 0, v___x_2489_);
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2489_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v_k_2427_);
lean_ctor_set(v_reuseFailAlloc_2499_, 2, v_v_2428_);
lean_ctor_set(v_reuseFailAlloc_2499_, 3, v_l_2429_);
lean_ctor_set(v_reuseFailAlloc_2499_, 4, v___x_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
}
else
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
lean_dec_ref_known(v_l_2429_, 5);
lean_del_object(v___x_2441_);
lean_dec(v_v_2428_);
lean_dec(v_k_2427_);
lean_dec(v_size_2426_);
lean_dec_ref_known(v_r_2419_, 5);
lean_del_object(v___x_2421_);
lean_dec(v_v_2417_);
lean_dec(v_k_2416_);
v___x_2507_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__3);
v___x_2508_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4___redArg(v___x_2507_);
return v___x_2508_;
}
}
else
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
lean_del_object(v___x_2441_);
lean_dec(v_r_2430_);
lean_dec(v_v_2428_);
lean_dec(v_k_2427_);
lean_dec(v_size_2426_);
lean_dec_ref_known(v_r_2419_, 5);
lean_del_object(v___x_2421_);
lean_dec(v_v_2417_);
lean_dec(v_k_2416_);
v___x_2509_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__4);
v___x_2510_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4___redArg(v___x_2509_);
return v___x_2510_;
}
}
}
}
else
{
lean_object* v_size_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2521_; 
v_size_2517_ = lean_ctor_get(v_r_2419_, 0);
v___x_2518_ = lean_unsigned_to_nat(1u);
v___x_2519_ = lean_nat_add(v___x_2518_, v_size_2517_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 3, v___x_2424_);
lean_ctor_set(v___x_2421_, 0, v___x_2519_);
v___x_2521_ = v___x_2421_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2519_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_k_2416_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v_v_2417_);
lean_ctor_set(v_reuseFailAlloc_2522_, 3, v___x_2424_);
lean_ctor_set(v_reuseFailAlloc_2522_, 4, v_r_2419_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
else
{
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_l_2523_; 
v_l_2523_ = lean_ctor_get(v___x_2424_, 3);
if (lean_obj_tag(v_l_2523_) == 0)
{
lean_object* v_r_2524_; 
lean_inc_ref(v_l_2523_);
v_r_2524_ = lean_ctor_get(v___x_2424_, 4);
lean_inc(v_r_2524_);
if (lean_obj_tag(v_r_2524_) == 0)
{
lean_object* v_size_2525_; lean_object* v_k_2526_; lean_object* v_v_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2541_; 
v_size_2525_ = lean_ctor_get(v___x_2424_, 0);
v_k_2526_ = lean_ctor_get(v___x_2424_, 1);
v_v_2527_ = lean_ctor_get(v___x_2424_, 2);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2541_ == 0)
{
lean_object* v_unused_2542_; lean_object* v_unused_2543_; 
v_unused_2542_ = lean_ctor_get(v___x_2424_, 4);
lean_dec(v_unused_2542_);
v_unused_2543_ = lean_ctor_get(v___x_2424_, 3);
lean_dec(v_unused_2543_);
v___x_2529_ = v___x_2424_;
v_isShared_2530_ = v_isSharedCheck_2541_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_v_2527_);
lean_inc(v_k_2526_);
lean_inc(v_size_2525_);
lean_dec(v___x_2424_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2541_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v_size_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2536_; 
v_size_2531_ = lean_ctor_get(v_r_2524_, 0);
v___x_2532_ = lean_unsigned_to_nat(1u);
v___x_2533_ = lean_nat_add(v___x_2532_, v_size_2525_);
lean_dec(v_size_2525_);
v___x_2534_ = lean_nat_add(v___x_2532_, v_size_2531_);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 4, v_r_2419_);
lean_ctor_set(v___x_2529_, 3, v_r_2524_);
lean_ctor_set(v___x_2529_, 2, v_v_2417_);
lean_ctor_set(v___x_2529_, 1, v_k_2416_);
lean_ctor_set(v___x_2529_, 0, v___x_2534_);
v___x_2536_ = v___x_2529_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2534_);
lean_ctor_set(v_reuseFailAlloc_2540_, 1, v_k_2416_);
lean_ctor_set(v_reuseFailAlloc_2540_, 2, v_v_2417_);
lean_ctor_set(v_reuseFailAlloc_2540_, 3, v_r_2524_);
lean_ctor_set(v_reuseFailAlloc_2540_, 4, v_r_2419_);
v___x_2536_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
lean_object* v___x_2538_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v___x_2536_);
lean_ctor_set(v___x_2421_, 3, v_l_2523_);
lean_ctor_set(v___x_2421_, 2, v_v_2527_);
lean_ctor_set(v___x_2421_, 1, v_k_2526_);
lean_ctor_set(v___x_2421_, 0, v___x_2533_);
v___x_2538_ = v___x_2421_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2533_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_k_2526_);
lean_ctor_set(v_reuseFailAlloc_2539_, 2, v_v_2527_);
lean_ctor_set(v_reuseFailAlloc_2539_, 3, v_l_2523_);
lean_ctor_set(v_reuseFailAlloc_2539_, 4, v___x_2536_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
else
{
lean_object* v_k_2544_; lean_object* v_v_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2557_; 
v_k_2544_ = lean_ctor_get(v___x_2424_, 1);
v_v_2545_ = lean_ctor_get(v___x_2424_, 2);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2557_ == 0)
{
lean_object* v_unused_2558_; lean_object* v_unused_2559_; lean_object* v_unused_2560_; 
v_unused_2558_ = lean_ctor_get(v___x_2424_, 4);
lean_dec(v_unused_2558_);
v_unused_2559_ = lean_ctor_get(v___x_2424_, 3);
lean_dec(v_unused_2559_);
v_unused_2560_ = lean_ctor_get(v___x_2424_, 0);
lean_dec(v_unused_2560_);
v___x_2547_ = v___x_2424_;
v_isShared_2548_ = v_isSharedCheck_2557_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_v_2545_);
lean_inc(v_k_2544_);
lean_dec(v___x_2424_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2557_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2552_; 
v___x_2549_ = lean_unsigned_to_nat(3u);
v___x_2550_ = lean_unsigned_to_nat(1u);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 3, v_r_2524_);
lean_ctor_set(v___x_2547_, 2, v_v_2417_);
lean_ctor_set(v___x_2547_, 1, v_k_2416_);
lean_ctor_set(v___x_2547_, 0, v___x_2550_);
v___x_2552_ = v___x_2547_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2550_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v_k_2416_);
lean_ctor_set(v_reuseFailAlloc_2556_, 2, v_v_2417_);
lean_ctor_set(v_reuseFailAlloc_2556_, 3, v_r_2524_);
lean_ctor_set(v_reuseFailAlloc_2556_, 4, v_r_2524_);
v___x_2552_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
lean_object* v___x_2554_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v___x_2552_);
lean_ctor_set(v___x_2421_, 3, v_l_2523_);
lean_ctor_set(v___x_2421_, 2, v_v_2545_);
lean_ctor_set(v___x_2421_, 1, v_k_2544_);
lean_ctor_set(v___x_2421_, 0, v___x_2549_);
v___x_2554_ = v___x_2421_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2549_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v_k_2544_);
lean_ctor_set(v_reuseFailAlloc_2555_, 2, v_v_2545_);
lean_ctor_set(v_reuseFailAlloc_2555_, 3, v_l_2523_);
lean_ctor_set(v_reuseFailAlloc_2555_, 4, v___x_2552_);
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
lean_object* v_r_2561_; 
v_r_2561_ = lean_ctor_get(v___x_2424_, 4);
lean_inc(v_r_2561_);
if (lean_obj_tag(v_r_2561_) == 0)
{
lean_object* v_k_2562_; lean_object* v_v_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2587_; 
lean_inc(v_l_2523_);
v_k_2562_ = lean_ctor_get(v___x_2424_, 1);
v_v_2563_ = lean_ctor_get(v___x_2424_, 2);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2587_ == 0)
{
lean_object* v_unused_2588_; lean_object* v_unused_2589_; lean_object* v_unused_2590_; 
v_unused_2588_ = lean_ctor_get(v___x_2424_, 4);
lean_dec(v_unused_2588_);
v_unused_2589_ = lean_ctor_get(v___x_2424_, 3);
lean_dec(v_unused_2589_);
v_unused_2590_ = lean_ctor_get(v___x_2424_, 0);
lean_dec(v_unused_2590_);
v___x_2565_ = v___x_2424_;
v_isShared_2566_ = v_isSharedCheck_2587_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_v_2563_);
lean_inc(v_k_2562_);
lean_dec(v___x_2424_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2587_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v_k_2567_; lean_object* v_v_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2583_; 
v_k_2567_ = lean_ctor_get(v_r_2561_, 1);
v_v_2568_ = lean_ctor_get(v_r_2561_, 2);
v_isSharedCheck_2583_ = !lean_is_exclusive(v_r_2561_);
if (v_isSharedCheck_2583_ == 0)
{
lean_object* v_unused_2584_; lean_object* v_unused_2585_; lean_object* v_unused_2586_; 
v_unused_2584_ = lean_ctor_get(v_r_2561_, 4);
lean_dec(v_unused_2584_);
v_unused_2585_ = lean_ctor_get(v_r_2561_, 3);
lean_dec(v_unused_2585_);
v_unused_2586_ = lean_ctor_get(v_r_2561_, 0);
lean_dec(v_unused_2586_);
v___x_2570_ = v_r_2561_;
v_isShared_2571_ = v_isSharedCheck_2583_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_v_2568_);
lean_inc(v_k_2567_);
lean_dec(v_r_2561_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2583_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2572_ = lean_unsigned_to_nat(3u);
v___x_2573_ = lean_unsigned_to_nat(1u);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 4, v_l_2523_);
lean_ctor_set(v___x_2570_, 3, v_l_2523_);
lean_ctor_set(v___x_2570_, 2, v_v_2563_);
lean_ctor_set(v___x_2570_, 1, v_k_2562_);
lean_ctor_set(v___x_2570_, 0, v___x_2573_);
v___x_2575_ = v___x_2570_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2573_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v_k_2562_);
lean_ctor_set(v_reuseFailAlloc_2582_, 2, v_v_2563_);
lean_ctor_set(v_reuseFailAlloc_2582_, 3, v_l_2523_);
lean_ctor_set(v_reuseFailAlloc_2582_, 4, v_l_2523_);
v___x_2575_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
lean_object* v___x_2577_; 
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 4, v_l_2523_);
lean_ctor_set(v___x_2565_, 2, v_v_2417_);
lean_ctor_set(v___x_2565_, 1, v_k_2416_);
lean_ctor_set(v___x_2565_, 0, v___x_2573_);
v___x_2577_ = v___x_2565_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2573_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_k_2416_);
lean_ctor_set(v_reuseFailAlloc_2581_, 2, v_v_2417_);
lean_ctor_set(v_reuseFailAlloc_2581_, 3, v_l_2523_);
lean_ctor_set(v_reuseFailAlloc_2581_, 4, v_l_2523_);
v___x_2577_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2579_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v___x_2577_);
lean_ctor_set(v___x_2421_, 3, v___x_2575_);
lean_ctor_set(v___x_2421_, 2, v_v_2568_);
lean_ctor_set(v___x_2421_, 1, v_k_2567_);
lean_ctor_set(v___x_2421_, 0, v___x_2572_);
v___x_2579_ = v___x_2421_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2572_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v_k_2567_);
lean_ctor_set(v_reuseFailAlloc_2580_, 2, v_v_2568_);
lean_ctor_set(v_reuseFailAlloc_2580_, 3, v___x_2575_);
lean_ctor_set(v_reuseFailAlloc_2580_, 4, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
}
}
else
{
lean_object* v___x_2591_; lean_object* v___x_2593_; 
v___x_2591_ = lean_unsigned_to_nat(2u);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v_r_2561_);
lean_ctor_set(v___x_2421_, 3, v___x_2424_);
lean_ctor_set(v___x_2421_, 0, v___x_2591_);
v___x_2593_ = v___x_2421_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2591_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v_k_2416_);
lean_ctor_set(v_reuseFailAlloc_2594_, 2, v_v_2417_);
lean_ctor_set(v_reuseFailAlloc_2594_, 3, v___x_2424_);
lean_ctor_set(v_reuseFailAlloc_2594_, 4, v_r_2561_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
else
{
lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2595_ = lean_unsigned_to_nat(1u);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v___x_2424_);
lean_ctor_set(v___x_2421_, 3, v___x_2424_);
lean_ctor_set(v___x_2421_, 0, v___x_2595_);
v___x_2597_ = v___x_2421_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_k_2416_);
lean_ctor_set(v_reuseFailAlloc_2598_, 2, v_v_2417_);
lean_ctor_set(v_reuseFailAlloc_2598_, 3, v___x_2424_);
lean_ctor_set(v_reuseFailAlloc_2598_, 4, v___x_2424_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
case 1:
{
lean_object* v___x_2600_; 
lean_dec(v_v_2417_);
lean_dec(v_k_2416_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 2, v_v_2413_);
lean_ctor_set(v___x_2421_, 1, v_k_2412_);
v___x_2600_ = v___x_2421_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_size_2415_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_k_2412_);
lean_ctor_set(v_reuseFailAlloc_2601_, 2, v_v_2413_);
lean_ctor_set(v_reuseFailAlloc_2601_, 3, v_l_2418_);
lean_ctor_set(v_reuseFailAlloc_2601_, 4, v_r_2419_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
default: 
{
lean_object* v___x_2602_; 
lean_dec(v_size_2415_);
v___x_2602_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg(v_k_2412_, v_v_2413_, v_r_2419_);
if (lean_obj_tag(v_l_2418_) == 0)
{
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_size_2603_; lean_object* v_size_2604_; lean_object* v_k_2605_; lean_object* v_v_2606_; lean_object* v_l_2607_; lean_object* v_r_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; uint8_t v___x_2611_; 
v_size_2603_ = lean_ctor_get(v_l_2418_, 0);
v_size_2604_ = lean_ctor_get(v___x_2602_, 0);
v_k_2605_ = lean_ctor_get(v___x_2602_, 1);
v_v_2606_ = lean_ctor_get(v___x_2602_, 2);
v_l_2607_ = lean_ctor_get(v___x_2602_, 3);
lean_inc(v_l_2607_);
v_r_2608_ = lean_ctor_get(v___x_2602_, 4);
v___x_2609_ = lean_unsigned_to_nat(3u);
v___x_2610_ = lean_nat_mul(v___x_2609_, v_size_2603_);
v___x_2611_ = lean_nat_dec_lt(v___x_2610_, v_size_2604_);
lean_dec(v___x_2610_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2616_; 
lean_dec(v_l_2607_);
v___x_2612_ = lean_unsigned_to_nat(1u);
v___x_2613_ = lean_nat_add(v___x_2612_, v_size_2603_);
v___x_2614_ = lean_nat_add(v___x_2613_, v_size_2604_);
lean_dec(v___x_2613_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v___x_2602_);
lean_ctor_set(v___x_2421_, 0, v___x_2614_);
v___x_2616_ = v___x_2421_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2614_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v_k_2416_);
lean_ctor_set(v_reuseFailAlloc_2617_, 2, v_v_2417_);
lean_ctor_set(v_reuseFailAlloc_2617_, 3, v_l_2418_);
lean_ctor_set(v_reuseFailAlloc_2617_, 4, v___x_2602_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
else
{
lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2687_; 
lean_inc(v_r_2608_);
lean_inc(v_v_2606_);
lean_inc(v_k_2605_);
lean_inc(v_size_2604_);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2687_ == 0)
{
lean_object* v_unused_2688_; lean_object* v_unused_2689_; lean_object* v_unused_2690_; lean_object* v_unused_2691_; lean_object* v_unused_2692_; 
v_unused_2688_ = lean_ctor_get(v___x_2602_, 4);
lean_dec(v_unused_2688_);
v_unused_2689_ = lean_ctor_get(v___x_2602_, 3);
lean_dec(v_unused_2689_);
v_unused_2690_ = lean_ctor_get(v___x_2602_, 2);
lean_dec(v_unused_2690_);
v_unused_2691_ = lean_ctor_get(v___x_2602_, 1);
lean_dec(v_unused_2691_);
v_unused_2692_ = lean_ctor_get(v___x_2602_, 0);
lean_dec(v_unused_2692_);
v___x_2619_ = v___x_2602_;
v_isShared_2620_ = v_isSharedCheck_2687_;
goto v_resetjp_2618_;
}
else
{
lean_dec(v___x_2602_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2687_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
if (lean_obj_tag(v_l_2607_) == 0)
{
if (lean_obj_tag(v_r_2608_) == 0)
{
lean_object* v_size_2621_; lean_object* v_k_2622_; lean_object* v_v_2623_; lean_object* v_l_2624_; lean_object* v_r_2625_; lean_object* v_size_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; 
v_size_2621_ = lean_ctor_get(v_l_2607_, 0);
v_k_2622_ = lean_ctor_get(v_l_2607_, 1);
v_v_2623_ = lean_ctor_get(v_l_2607_, 2);
v_l_2624_ = lean_ctor_get(v_l_2607_, 3);
v_r_2625_ = lean_ctor_get(v_l_2607_, 4);
v_size_2626_ = lean_ctor_get(v_r_2608_, 0);
v___x_2627_ = lean_unsigned_to_nat(2u);
v___x_2628_ = lean_nat_mul(v___x_2627_, v_size_2626_);
v___x_2629_ = lean_nat_dec_lt(v_size_2621_, v___x_2628_);
lean_dec(v___x_2628_);
if (v___x_2629_ == 0)
{
lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2658_; 
lean_inc(v_r_2625_);
lean_inc(v_l_2624_);
lean_inc(v_v_2623_);
lean_inc(v_k_2622_);
v_isSharedCheck_2658_ = !lean_is_exclusive(v_l_2607_);
if (v_isSharedCheck_2658_ == 0)
{
lean_object* v_unused_2659_; lean_object* v_unused_2660_; lean_object* v_unused_2661_; lean_object* v_unused_2662_; lean_object* v_unused_2663_; 
v_unused_2659_ = lean_ctor_get(v_l_2607_, 4);
lean_dec(v_unused_2659_);
v_unused_2660_ = lean_ctor_get(v_l_2607_, 3);
lean_dec(v_unused_2660_);
v_unused_2661_ = lean_ctor_get(v_l_2607_, 2);
lean_dec(v_unused_2661_);
v_unused_2662_ = lean_ctor_get(v_l_2607_, 1);
lean_dec(v_unused_2662_);
v_unused_2663_ = lean_ctor_get(v_l_2607_, 0);
lean_dec(v_unused_2663_);
v___x_2631_ = v_l_2607_;
v_isShared_2632_ = v_isSharedCheck_2658_;
goto v_resetjp_2630_;
}
else
{
lean_dec(v_l_2607_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2658_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2648_; 
v___x_2633_ = lean_unsigned_to_nat(1u);
v___x_2634_ = lean_nat_add(v___x_2633_, v_size_2603_);
v___x_2635_ = lean_nat_add(v___x_2634_, v_size_2604_);
lean_dec(v_size_2604_);
if (lean_obj_tag(v_l_2624_) == 0)
{
lean_object* v_size_2656_; 
v_size_2656_ = lean_ctor_get(v_l_2624_, 0);
lean_inc(v_size_2656_);
v___y_2648_ = v_size_2656_;
goto v___jp_2647_;
}
else
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_unsigned_to_nat(0u);
v___y_2648_ = v___x_2657_;
goto v___jp_2647_;
}
v___jp_2636_:
{
lean_object* v___x_2640_; lean_object* v___x_2642_; 
v___x_2640_ = lean_nat_add(v___y_2637_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec(v___y_2637_);
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 4, v_r_2608_);
lean_ctor_set(v___x_2631_, 3, v_r_2625_);
lean_ctor_set(v___x_2631_, 2, v_v_2606_);
lean_ctor_set(v___x_2631_, 1, v_k_2605_);
lean_ctor_set(v___x_2631_, 0, v___x_2640_);
v___x_2642_ = v___x_2631_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2640_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v_k_2605_);
lean_ctor_set(v_reuseFailAlloc_2646_, 2, v_v_2606_);
lean_ctor_set(v_reuseFailAlloc_2646_, 3, v_r_2625_);
lean_ctor_set(v_reuseFailAlloc_2646_, 4, v_r_2608_);
v___x_2642_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
lean_object* v___x_2644_; 
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 4, v___x_2642_);
lean_ctor_set(v___x_2619_, 3, v___y_2638_);
lean_ctor_set(v___x_2619_, 2, v_v_2623_);
lean_ctor_set(v___x_2619_, 1, v_k_2622_);
lean_ctor_set(v___x_2619_, 0, v___x_2635_);
v___x_2644_ = v___x_2619_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2635_);
lean_ctor_set(v_reuseFailAlloc_2645_, 1, v_k_2622_);
lean_ctor_set(v_reuseFailAlloc_2645_, 2, v_v_2623_);
lean_ctor_set(v_reuseFailAlloc_2645_, 3, v___y_2638_);
lean_ctor_set(v_reuseFailAlloc_2645_, 4, v___x_2642_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
v___jp_2647_:
{
lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2649_ = lean_nat_add(v___x_2634_, v___y_2648_);
lean_dec(v___y_2648_);
lean_dec(v___x_2634_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v_l_2624_);
lean_ctor_set(v___x_2421_, 0, v___x_2649_);
v___x_2651_ = v___x_2421_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v_k_2416_);
lean_ctor_set(v_reuseFailAlloc_2655_, 2, v_v_2417_);
lean_ctor_set(v_reuseFailAlloc_2655_, 3, v_l_2418_);
lean_ctor_set(v_reuseFailAlloc_2655_, 4, v_l_2624_);
v___x_2651_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2652_; 
v___x_2652_ = lean_nat_add(v___x_2633_, v_size_2626_);
if (lean_obj_tag(v_r_2625_) == 0)
{
lean_object* v_size_2653_; 
v_size_2653_ = lean_ctor_get(v_r_2625_, 0);
lean_inc(v_size_2653_);
v___y_2637_ = v___x_2652_;
v___y_2638_ = v___x_2651_;
v___y_2639_ = v_size_2653_;
goto v___jp_2636_;
}
else
{
lean_object* v___x_2654_; 
v___x_2654_ = lean_unsigned_to_nat(0u);
v___y_2637_ = v___x_2652_;
v___y_2638_ = v___x_2651_;
v___y_2639_ = v___x_2654_;
goto v___jp_2636_;
}
}
}
}
}
else
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2669_; 
lean_del_object(v___x_2421_);
v___x_2664_ = lean_unsigned_to_nat(1u);
v___x_2665_ = lean_nat_add(v___x_2664_, v_size_2603_);
v___x_2666_ = lean_nat_add(v___x_2665_, v_size_2604_);
lean_dec(v_size_2604_);
v___x_2667_ = lean_nat_add(v___x_2665_, v_size_2621_);
lean_dec(v___x_2665_);
lean_inc_ref(v_l_2418_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 4, v_l_2607_);
lean_ctor_set(v___x_2619_, 3, v_l_2418_);
lean_ctor_set(v___x_2619_, 2, v_v_2417_);
lean_ctor_set(v___x_2619_, 1, v_k_2416_);
lean_ctor_set(v___x_2619_, 0, v___x_2667_);
v___x_2669_ = v___x_2619_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2667_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_k_2416_);
lean_ctor_set(v_reuseFailAlloc_2682_, 2, v_v_2417_);
lean_ctor_set(v_reuseFailAlloc_2682_, 3, v_l_2418_);
lean_ctor_set(v_reuseFailAlloc_2682_, 4, v_l_2607_);
v___x_2669_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
v_isSharedCheck_2676_ = !lean_is_exclusive(v_l_2418_);
if (v_isSharedCheck_2676_ == 0)
{
lean_object* v_unused_2677_; lean_object* v_unused_2678_; lean_object* v_unused_2679_; lean_object* v_unused_2680_; lean_object* v_unused_2681_; 
v_unused_2677_ = lean_ctor_get(v_l_2418_, 4);
lean_dec(v_unused_2677_);
v_unused_2678_ = lean_ctor_get(v_l_2418_, 3);
lean_dec(v_unused_2678_);
v_unused_2679_ = lean_ctor_get(v_l_2418_, 2);
lean_dec(v_unused_2679_);
v_unused_2680_ = lean_ctor_get(v_l_2418_, 1);
lean_dec(v_unused_2680_);
v_unused_2681_ = lean_ctor_get(v_l_2418_, 0);
lean_dec(v_unused_2681_);
v___x_2671_ = v_l_2418_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_dec(v_l_2418_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 4, v_r_2608_);
lean_ctor_set(v___x_2671_, 3, v___x_2669_);
lean_ctor_set(v___x_2671_, 2, v_v_2606_);
lean_ctor_set(v___x_2671_, 1, v_k_2605_);
lean_ctor_set(v___x_2671_, 0, v___x_2666_);
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2666_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v_k_2605_);
lean_ctor_set(v_reuseFailAlloc_2675_, 2, v_v_2606_);
lean_ctor_set(v_reuseFailAlloc_2675_, 3, v___x_2669_);
lean_ctor_set(v_reuseFailAlloc_2675_, 4, v_r_2608_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
}
else
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
lean_dec_ref_known(v_l_2607_, 5);
lean_del_object(v___x_2619_);
lean_dec(v_v_2606_);
lean_dec(v_k_2605_);
lean_dec(v_size_2604_);
lean_dec_ref_known(v_l_2418_, 5);
lean_del_object(v___x_2421_);
lean_dec(v_v_2417_);
lean_dec(v_k_2416_);
v___x_2683_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__7);
v___x_2684_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4___redArg(v___x_2683_);
return v___x_2684_;
}
}
else
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
lean_del_object(v___x_2619_);
lean_dec(v_r_2608_);
lean_dec(v_v_2606_);
lean_dec(v_k_2605_);
lean_dec(v_size_2604_);
lean_dec_ref_known(v_l_2418_, 5);
lean_del_object(v___x_2421_);
lean_dec(v_v_2417_);
lean_dec(v_k_2416_);
v___x_2685_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg___closed__8);
v___x_2686_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4___redArg(v___x_2685_);
return v___x_2686_;
}
}
}
}
else
{
lean_object* v_size_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2697_; 
v_size_2693_ = lean_ctor_get(v_l_2418_, 0);
v___x_2694_ = lean_unsigned_to_nat(1u);
v___x_2695_ = lean_nat_add(v___x_2694_, v_size_2693_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v___x_2602_);
lean_ctor_set(v___x_2421_, 0, v___x_2695_);
v___x_2697_ = v___x_2421_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2695_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_k_2416_);
lean_ctor_set(v_reuseFailAlloc_2698_, 2, v_v_2417_);
lean_ctor_set(v_reuseFailAlloc_2698_, 3, v_l_2418_);
lean_ctor_set(v_reuseFailAlloc_2698_, 4, v___x_2602_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
else
{
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_l_2699_; 
v_l_2699_ = lean_ctor_get(v___x_2602_, 3);
lean_inc(v_l_2699_);
if (lean_obj_tag(v_l_2699_) == 0)
{
lean_object* v_r_2700_; 
v_r_2700_ = lean_ctor_get(v___x_2602_, 4);
lean_inc(v_r_2700_);
if (lean_obj_tag(v_r_2700_) == 0)
{
lean_object* v_size_2701_; lean_object* v_k_2702_; lean_object* v_v_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2717_; 
v_size_2701_ = lean_ctor_get(v___x_2602_, 0);
v_k_2702_ = lean_ctor_get(v___x_2602_, 1);
v_v_2703_ = lean_ctor_get(v___x_2602_, 2);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2717_ == 0)
{
lean_object* v_unused_2718_; lean_object* v_unused_2719_; 
v_unused_2718_ = lean_ctor_get(v___x_2602_, 4);
lean_dec(v_unused_2718_);
v_unused_2719_ = lean_ctor_get(v___x_2602_, 3);
lean_dec(v_unused_2719_);
v___x_2705_ = v___x_2602_;
v_isShared_2706_ = v_isSharedCheck_2717_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_v_2703_);
lean_inc(v_k_2702_);
lean_inc(v_size_2701_);
lean_dec(v___x_2602_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2717_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v_size_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2712_; 
v_size_2707_ = lean_ctor_get(v_l_2699_, 0);
v___x_2708_ = lean_unsigned_to_nat(1u);
v___x_2709_ = lean_nat_add(v___x_2708_, v_size_2701_);
lean_dec(v_size_2701_);
v___x_2710_ = lean_nat_add(v___x_2708_, v_size_2707_);
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 4, v_l_2699_);
lean_ctor_set(v___x_2705_, 3, v_l_2418_);
lean_ctor_set(v___x_2705_, 2, v_v_2417_);
lean_ctor_set(v___x_2705_, 1, v_k_2416_);
lean_ctor_set(v___x_2705_, 0, v___x_2710_);
v___x_2712_ = v___x_2705_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___x_2710_);
lean_ctor_set(v_reuseFailAlloc_2716_, 1, v_k_2416_);
lean_ctor_set(v_reuseFailAlloc_2716_, 2, v_v_2417_);
lean_ctor_set(v_reuseFailAlloc_2716_, 3, v_l_2418_);
lean_ctor_set(v_reuseFailAlloc_2716_, 4, v_l_2699_);
v___x_2712_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
lean_object* v___x_2714_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v_r_2700_);
lean_ctor_set(v___x_2421_, 3, v___x_2712_);
lean_ctor_set(v___x_2421_, 2, v_v_2703_);
lean_ctor_set(v___x_2421_, 1, v_k_2702_);
lean_ctor_set(v___x_2421_, 0, v___x_2709_);
v___x_2714_ = v___x_2421_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2709_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v_k_2702_);
lean_ctor_set(v_reuseFailAlloc_2715_, 2, v_v_2703_);
lean_ctor_set(v_reuseFailAlloc_2715_, 3, v___x_2712_);
lean_ctor_set(v_reuseFailAlloc_2715_, 4, v_r_2700_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
else
{
lean_object* v_k_2720_; lean_object* v_v_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2745_; 
v_k_2720_ = lean_ctor_get(v___x_2602_, 1);
v_v_2721_ = lean_ctor_get(v___x_2602_, 2);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2745_ == 0)
{
lean_object* v_unused_2746_; lean_object* v_unused_2747_; lean_object* v_unused_2748_; 
v_unused_2746_ = lean_ctor_get(v___x_2602_, 4);
lean_dec(v_unused_2746_);
v_unused_2747_ = lean_ctor_get(v___x_2602_, 3);
lean_dec(v_unused_2747_);
v_unused_2748_ = lean_ctor_get(v___x_2602_, 0);
lean_dec(v_unused_2748_);
v___x_2723_ = v___x_2602_;
v_isShared_2724_ = v_isSharedCheck_2745_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_v_2721_);
lean_inc(v_k_2720_);
lean_dec(v___x_2602_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2745_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v_k_2725_; lean_object* v_v_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2741_; 
v_k_2725_ = lean_ctor_get(v_l_2699_, 1);
v_v_2726_ = lean_ctor_get(v_l_2699_, 2);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_l_2699_);
if (v_isSharedCheck_2741_ == 0)
{
lean_object* v_unused_2742_; lean_object* v_unused_2743_; lean_object* v_unused_2744_; 
v_unused_2742_ = lean_ctor_get(v_l_2699_, 4);
lean_dec(v_unused_2742_);
v_unused_2743_ = lean_ctor_get(v_l_2699_, 3);
lean_dec(v_unused_2743_);
v_unused_2744_ = lean_ctor_get(v_l_2699_, 0);
lean_dec(v_unused_2744_);
v___x_2728_ = v_l_2699_;
v_isShared_2729_ = v_isSharedCheck_2741_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_v_2726_);
lean_inc(v_k_2725_);
lean_dec(v_l_2699_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2741_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2733_; 
v___x_2730_ = lean_unsigned_to_nat(3u);
v___x_2731_ = lean_unsigned_to_nat(1u);
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 4, v_r_2700_);
lean_ctor_set(v___x_2728_, 3, v_r_2700_);
lean_ctor_set(v___x_2728_, 2, v_v_2417_);
lean_ctor_set(v___x_2728_, 1, v_k_2416_);
lean_ctor_set(v___x_2728_, 0, v___x_2731_);
v___x_2733_ = v___x_2728_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2731_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v_k_2416_);
lean_ctor_set(v_reuseFailAlloc_2740_, 2, v_v_2417_);
lean_ctor_set(v_reuseFailAlloc_2740_, 3, v_r_2700_);
lean_ctor_set(v_reuseFailAlloc_2740_, 4, v_r_2700_);
v___x_2733_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
lean_object* v___x_2735_; 
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 3, v_r_2700_);
lean_ctor_set(v___x_2723_, 0, v___x_2731_);
v___x_2735_ = v___x_2723_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2731_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_k_2720_);
lean_ctor_set(v_reuseFailAlloc_2739_, 2, v_v_2721_);
lean_ctor_set(v_reuseFailAlloc_2739_, 3, v_r_2700_);
lean_ctor_set(v_reuseFailAlloc_2739_, 4, v_r_2700_);
v___x_2735_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___x_2737_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v___x_2735_);
lean_ctor_set(v___x_2421_, 3, v___x_2733_);
lean_ctor_set(v___x_2421_, 2, v_v_2726_);
lean_ctor_set(v___x_2421_, 1, v_k_2725_);
lean_ctor_set(v___x_2421_, 0, v___x_2730_);
v___x_2737_ = v___x_2421_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v___x_2730_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v_k_2725_);
lean_ctor_set(v_reuseFailAlloc_2738_, 2, v_v_2726_);
lean_ctor_set(v_reuseFailAlloc_2738_, 3, v___x_2733_);
lean_ctor_set(v_reuseFailAlloc_2738_, 4, v___x_2735_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_2749_; 
v_r_2749_ = lean_ctor_get(v___x_2602_, 4);
lean_inc(v_r_2749_);
if (lean_obj_tag(v_r_2749_) == 0)
{
lean_object* v_k_2750_; lean_object* v_v_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2763_; 
v_k_2750_ = lean_ctor_get(v___x_2602_, 1);
v_v_2751_ = lean_ctor_get(v___x_2602_, 2);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2763_ == 0)
{
lean_object* v_unused_2764_; lean_object* v_unused_2765_; lean_object* v_unused_2766_; 
v_unused_2764_ = lean_ctor_get(v___x_2602_, 4);
lean_dec(v_unused_2764_);
v_unused_2765_ = lean_ctor_get(v___x_2602_, 3);
lean_dec(v_unused_2765_);
v_unused_2766_ = lean_ctor_get(v___x_2602_, 0);
lean_dec(v_unused_2766_);
v___x_2753_ = v___x_2602_;
v_isShared_2754_ = v_isSharedCheck_2763_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_v_2751_);
lean_inc(v_k_2750_);
lean_dec(v___x_2602_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2763_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2758_; 
v___x_2755_ = lean_unsigned_to_nat(3u);
v___x_2756_ = lean_unsigned_to_nat(1u);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 4, v_l_2699_);
lean_ctor_set(v___x_2753_, 2, v_v_2417_);
lean_ctor_set(v___x_2753_, 1, v_k_2416_);
lean_ctor_set(v___x_2753_, 0, v___x_2756_);
v___x_2758_ = v___x_2753_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2756_);
lean_ctor_set(v_reuseFailAlloc_2762_, 1, v_k_2416_);
lean_ctor_set(v_reuseFailAlloc_2762_, 2, v_v_2417_);
lean_ctor_set(v_reuseFailAlloc_2762_, 3, v_l_2699_);
lean_ctor_set(v_reuseFailAlloc_2762_, 4, v_l_2699_);
v___x_2758_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
lean_object* v___x_2760_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v_r_2749_);
lean_ctor_set(v___x_2421_, 3, v___x_2758_);
lean_ctor_set(v___x_2421_, 2, v_v_2751_);
lean_ctor_set(v___x_2421_, 1, v_k_2750_);
lean_ctor_set(v___x_2421_, 0, v___x_2755_);
v___x_2760_ = v___x_2421_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___x_2755_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v_k_2750_);
lean_ctor_set(v_reuseFailAlloc_2761_, 2, v_v_2751_);
lean_ctor_set(v_reuseFailAlloc_2761_, 3, v___x_2758_);
lean_ctor_set(v_reuseFailAlloc_2761_, 4, v_r_2749_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
else
{
lean_object* v___x_2767_; lean_object* v___x_2769_; 
v___x_2767_ = lean_unsigned_to_nat(2u);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v___x_2602_);
lean_ctor_set(v___x_2421_, 3, v_r_2749_);
lean_ctor_set(v___x_2421_, 0, v___x_2767_);
v___x_2769_ = v___x_2421_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v___x_2767_);
lean_ctor_set(v_reuseFailAlloc_2770_, 1, v_k_2416_);
lean_ctor_set(v_reuseFailAlloc_2770_, 2, v_v_2417_);
lean_ctor_set(v_reuseFailAlloc_2770_, 3, v_r_2749_);
lean_ctor_set(v_reuseFailAlloc_2770_, 4, v___x_2602_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
else
{
lean_object* v___x_2771_; lean_object* v___x_2773_; 
v___x_2771_ = lean_unsigned_to_nat(1u);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v___x_2602_);
lean_ctor_set(v___x_2421_, 3, v___x_2602_);
lean_ctor_set(v___x_2421_, 0, v___x_2771_);
v___x_2773_ = v___x_2421_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v_k_2416_);
lean_ctor_set(v_reuseFailAlloc_2774_, 2, v_v_2417_);
lean_ctor_set(v_reuseFailAlloc_2774_, 3, v___x_2602_);
lean_ctor_set(v_reuseFailAlloc_2774_, 4, v___x_2602_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2776_ = lean_unsigned_to_nat(1u);
v___x_2777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2776_);
lean_ctor_set(v___x_2777_, 1, v_k_2412_);
lean_ctor_set(v___x_2777_, 2, v_v_2413_);
lean_ctor_set(v___x_2777_, 3, v_t_2414_);
lean_ctor_set(v___x_2777_, 4, v_t_2414_);
return v___x_2777_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__3_spec__6(lean_object* v_init_2778_, lean_object* v_x_2779_){
_start:
{
if (lean_obj_tag(v_x_2779_) == 0)
{
lean_object* v_k_2780_; lean_object* v_v_2781_; lean_object* v_l_2782_; lean_object* v_r_2783_; lean_object* v___x_2784_; uint8_t v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v_k_2780_ = lean_ctor_get(v_x_2779_, 1);
lean_inc(v_k_2780_);
v_v_2781_ = lean_ctor_get(v_x_2779_, 2);
lean_inc(v_v_2781_);
v_l_2782_ = lean_ctor_get(v_x_2779_, 3);
lean_inc(v_l_2782_);
v_r_2783_ = lean_ctor_get(v_x_2779_, 4);
lean_inc(v_r_2783_);
lean_dec_ref_known(v_x_2779_, 5);
v___x_2784_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__3_spec__6(v_init_2778_, v_l_2782_);
v___x_2785_ = 1;
v___x_2786_ = l_Lean_Name_toString(v_k_2780_, v___x_2785_);
v___x_2787_ = l_Lean_Array_toJson___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1(v_v_2781_);
v___x_2788_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg(v___x_2786_, v___x_2787_, v___x_2784_);
v_init_2778_ = v___x_2788_;
v_x_2779_ = v_r_2783_;
goto _start;
}
else
{
return v_init_2778_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1(lean_object* v_m_2790_){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2791_ = lean_box(1);
v___x_2792_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__3_spec__6(v___x_2791_, v_m_2790_);
v___x_2793_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonModuleSetup_toJson_spec__0(lean_object* v_k_2794_, lean_object* v_x_2795_){
_start:
{
if (lean_obj_tag(v_x_2795_) == 0)
{
lean_object* v___x_2796_; 
lean_dec_ref(v_k_2794_);
v___x_2796_ = lean_box(0);
return v___x_2796_;
}
else
{
lean_object* v_val_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v_val_2797_ = lean_ctor_get(v_x_2795_, 0);
lean_inc(v_val_2797_);
lean_dec_ref_known(v_x_2795_, 1);
v___x_2798_ = l_Lean_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0(v_val_2797_);
v___x_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2799_, 0, v_k_2794_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
v___x_2800_ = lean_box(0);
v___x_2801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2799_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
return v___x_2801_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__9_spec__13(lean_object* v_init_2802_, lean_object* v_x_2803_){
_start:
{
if (lean_obj_tag(v_x_2803_) == 0)
{
lean_object* v_k_2804_; lean_object* v_v_2805_; lean_object* v_l_2806_; lean_object* v_r_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; lean_object* v___x_2810_; lean_object* v___y_2812_; 
v_k_2804_ = lean_ctor_get(v_x_2803_, 1);
lean_inc(v_k_2804_);
v_v_2805_ = lean_ctor_get(v_x_2803_, 2);
lean_inc(v_v_2805_);
v_l_2806_ = lean_ctor_get(v_x_2803_, 3);
lean_inc(v_l_2806_);
v_r_2807_ = lean_ctor_get(v_x_2803_, 4);
lean_inc(v_r_2807_);
lean_dec_ref_known(v_x_2803_, 5);
v___x_2808_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__9_spec__13(v_init_2802_, v_l_2806_);
v___x_2809_ = 1;
v___x_2810_ = l_Lean_Name_toString(v_k_2804_, v___x_2809_);
switch(lean_obj_tag(v_v_2805_))
{
case 0:
{
lean_object* v_s_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
v_s_2815_ = lean_ctor_get(v_v_2805_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v_v_2805_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v_v_2805_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_s_2815_);
lean_dec(v_v_2805_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
lean_ctor_set_tag(v___x_2817_, 3);
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_s_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
v___y_2812_ = v___x_2820_;
goto v___jp_2811_;
}
}
}
case 1:
{
uint8_t v_b_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
v_b_2823_ = lean_ctor_get_uint8(v_v_2805_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v_v_2805_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v_v_2805_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_dec(v_v_2805_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2829_, 0, v_b_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
v___y_2812_ = v___x_2828_;
goto v___jp_2811_;
}
}
}
default: 
{
lean_object* v_n_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2839_; 
v_n_2831_ = lean_ctor_get(v_v_2805_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v_v_2805_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2833_ = v_v_2805_;
v_isShared_2834_ = v_isSharedCheck_2839_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_n_2831_);
lean_dec(v_v_2805_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2839_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2835_; lean_object* v___x_2837_; 
v___x_2835_ = l_Lean_JsonNumber_fromNat(v_n_2831_);
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 0, v___x_2835_);
v___x_2837_ = v___x_2833_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v___x_2835_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
v___y_2812_ = v___x_2837_;
goto v___jp_2811_;
}
}
}
}
v___jp_2811_:
{
lean_object* v___x_2813_; 
v___x_2813_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg(v___x_2810_, v___y_2812_, v___x_2808_);
v_init_2802_ = v___x_2813_;
v_x_2803_ = v_r_2807_;
goto _start;
}
}
else
{
return v_init_2802_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4(lean_object* v_m_2840_){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2841_ = lean_box(1);
v___x_2842_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__9_spec__13(v___x_2841_, v_m_2840_);
v___x_2843_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__7(size_t v_sz_2844_, size_t v_i_2845_, lean_object* v_bs_2846_){
_start:
{
uint8_t v___x_2847_; 
v___x_2847_ = lean_usize_dec_lt(v_i_2845_, v_sz_2844_);
if (v___x_2847_ == 0)
{
return v_bs_2846_;
}
else
{
lean_object* v_v_2848_; lean_object* v___x_2849_; lean_object* v_bs_x27_2850_; lean_object* v___x_2851_; size_t v___x_2852_; size_t v___x_2853_; lean_object* v___x_2854_; 
v_v_2848_ = lean_array_uget(v_bs_2846_, v_i_2845_);
v___x_2849_ = lean_unsigned_to_nat(0u);
v_bs_x27_2850_ = lean_array_uset(v_bs_2846_, v_i_2845_, v___x_2849_);
v___x_2851_ = l_Lean_instToJsonPlugin_toJson(v_v_2848_);
v___x_2852_ = ((size_t)1ULL);
v___x_2853_ = lean_usize_add(v_i_2845_, v___x_2852_);
v___x_2854_ = lean_array_uset(v_bs_x27_2850_, v_i_2845_, v___x_2851_);
v_i_2845_ = v___x_2853_;
v_bs_2846_ = v___x_2854_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__7___boxed(lean_object* v_sz_2856_, lean_object* v_i_2857_, lean_object* v_bs_2858_){
_start:
{
size_t v_sz_boxed_2859_; size_t v_i_boxed_2860_; lean_object* v_res_2861_; 
v_sz_boxed_2859_ = lean_unbox_usize(v_sz_2856_);
lean_dec(v_sz_2856_);
v_i_boxed_2860_ = lean_unbox_usize(v_i_2857_);
lean_dec(v_i_2857_);
v_res_2861_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__7(v_sz_boxed_2859_, v_i_boxed_2860_, v_bs_2858_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3(lean_object* v_a_2862_){
_start:
{
size_t v_sz_2863_; size_t v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v_sz_2863_ = lean_array_size(v_a_2862_);
v___x_2864_ = ((size_t)0ULL);
v___x_2865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__7(v_sz_2863_, v___x_2864_, v_a_2862_);
v___x_2866_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonModuleSetup_toJson(lean_object* v_x_2868_){
_start:
{
lean_object* v_name_2869_; lean_object* v_package_x3f_2870_; uint8_t v_isModule_2871_; lean_object* v_imports_x3f_2872_; lean_object* v_importArts_2873_; lean_object* v_dynlibs_2874_; lean_object* v_plugins_2875_; lean_object* v_options_2876_; lean_object* v___x_2877_; uint8_t v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v_name_2869_ = lean_ctor_get(v_x_2868_, 0);
lean_inc(v_name_2869_);
v_package_x3f_2870_ = lean_ctor_get(v_x_2868_, 1);
lean_inc(v_package_x3f_2870_);
v_isModule_2871_ = lean_ctor_get_uint8(v_x_2868_, sizeof(void*)*7);
v_imports_x3f_2872_ = lean_ctor_get(v_x_2868_, 2);
lean_inc(v_imports_x3f_2872_);
v_importArts_2873_ = lean_ctor_get(v_x_2868_, 3);
lean_inc(v_importArts_2873_);
v_dynlibs_2874_ = lean_ctor_get(v_x_2868_, 4);
lean_inc_ref(v_dynlibs_2874_);
v_plugins_2875_ = lean_ctor_get(v_x_2868_, 5);
lean_inc_ref(v_plugins_2875_);
v_options_2876_ = lean_ctor_get(v_x_2868_, 6);
lean_inc(v_options_2876_);
lean_dec_ref(v_x_2868_);
v___x_2877_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__0));
v___x_2878_ = 1;
v___x_2879_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2869_, v___x_2878_);
v___x_2880_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
v___x_2881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2877_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v___x_2882_ = lean_box(0);
v___x_2883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2881_);
lean_ctor_set(v___x_2883_, 1, v___x_2882_);
v___x_2884_ = ((lean_object*)(l_Lean_instToJsonModuleSetup_toJson___closed__0));
v___x_2885_ = l_Lean_Json_opt___at___00Lean_instToJsonPlugin_toJson_spec__0(v___x_2884_, v_package_x3f_2870_);
v___x_2886_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__5));
v___x_2887_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2887_, 0, v_isModule_2871_);
v___x_2888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2886_);
lean_ctor_set(v___x_2888_, 1, v___x_2887_);
v___x_2889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2888_);
lean_ctor_set(v___x_2889_, 1, v___x_2882_);
v___x_2890_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__0));
v___x_2891_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleSetup_toJson_spec__0(v___x_2890_, v_imports_x3f_2872_);
v___x_2892_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__8));
v___x_2893_ = l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1(v_importArts_2873_);
v___x_2894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2892_);
lean_ctor_set(v___x_2894_, 1, v___x_2893_);
v___x_2895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2894_);
lean_ctor_set(v___x_2895_, 1, v___x_2882_);
v___x_2896_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__12));
v___x_2897_ = l_Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2(v_dynlibs_2874_);
v___x_2898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2896_);
lean_ctor_set(v___x_2898_, 1, v___x_2897_);
v___x_2899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
lean_ctor_set(v___x_2899_, 1, v___x_2882_);
v___x_2900_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__14));
v___x_2901_ = l_Lean_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3(v_plugins_2875_);
v___x_2902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2900_);
lean_ctor_set(v___x_2902_, 1, v___x_2901_);
v___x_2903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2902_);
lean_ctor_set(v___x_2903_, 1, v___x_2882_);
v___x_2904_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__16));
v___x_2905_ = l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4(v_options_2876_);
v___x_2906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2904_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
v___x_2907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
lean_ctor_set(v___x_2907_, 1, v___x_2882_);
v___x_2908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2907_);
lean_ctor_set(v___x_2908_, 1, v___x_2882_);
v___x_2909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2903_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
v___x_2910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2899_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
v___x_2911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2895_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
v___x_2912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2891_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
v___x_2913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2889_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
v___x_2914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2885_);
lean_ctor_set(v___x_2914_, 1, v___x_2913_);
v___x_2915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2883_);
lean_ctor_set(v___x_2915_, 1, v___x_2914_);
v___x_2916_ = ((lean_object*)(l_Lean_instToJsonImport_toJson___closed__0));
v___x_2917_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(v___x_2915_, v___x_2916_);
v___x_2918_ = l_Lean_Json_mkObj(v___x_2917_);
lean_dec(v___x_2917_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2919_, lean_object* v_msg_2920_){
_start:
{
lean_object* v___x_2921_; 
v___x_2921_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4___redArg(v_msg_2920_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2(lean_object* v_00_u03b2_2922_, lean_object* v_k_2923_, lean_object* v_v_2924_, lean_object* v_t_2925_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2___redArg(v_k_2923_, v_v_2924_, v_t_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__3(lean_object* v_init_2927_, lean_object* v_t_2928_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__3_spec__6(v_init_2927_, v_t_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__9(lean_object* v_init_2930_, lean_object* v_t_2931_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__9_spec__13(v_init_2930_, v_t_2931_);
return v___x_2932_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3(void){
_start:
{
lean_object* v_natZero_2939_; lean_object* v_intZero_2940_; 
v_natZero_2939_ = lean_unsigned_to_nat(0u);
v_intZero_2940_ = lean_nat_to_int(v_natZero_2939_);
return v_intZero_2940_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13(lean_object* v_init_2942_, lean_object* v_x_2943_){
_start:
{
if (lean_obj_tag(v_x_2943_) == 0)
{
lean_object* v_k_2948_; lean_object* v_v_2949_; lean_object* v_l_2950_; lean_object* v_r_2951_; lean_object* v___x_2952_; 
v_k_2948_ = lean_ctor_get(v_x_2943_, 1);
lean_inc(v_k_2948_);
v_v_2949_ = lean_ctor_get(v_x_2943_, 2);
lean_inc(v_v_2949_);
v_l_2950_ = lean_ctor_get(v_x_2943_, 3);
lean_inc(v_l_2950_);
v_r_2951_ = lean_ctor_get(v_x_2943_, 4);
lean_inc(v_r_2951_);
lean_dec_ref_known(v_x_2943_, 5);
v___x_2952_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13(v_init_2942_, v_l_2950_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_dec(v_r_2951_);
lean_dec(v_v_2949_);
lean_dec(v_k_2948_);
return v___x_2952_;
}
else
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_3039_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_2955_ = v___x_2952_;
v_isShared_2956_ = v_isSharedCheck_3039_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2952_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_3039_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v_a_2958_; lean_object* v___x_2962_; uint8_t v___x_2963_; 
v___x_2962_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__2));
v___x_2963_ = lean_string_dec_eq(v_k_2948_, v___x_2962_);
if (v___x_2963_ == 0)
{
lean_object* v_n_2964_; lean_object* v_a_2966_; uint8_t v___x_2969_; 
lean_inc(v_k_2948_);
v_n_2964_ = l_String_toName(v_k_2948_);
v___x_2969_ = l_Lean_Name_isAnonymous(v_n_2964_);
if (v___x_2969_ == 0)
{
lean_del_object(v___x_2955_);
lean_dec(v_k_2948_);
switch(lean_obj_tag(v_v_2949_))
{
case 3:
{
lean_object* v_s_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
v_s_2970_ = lean_ctor_get(v_v_2949_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_v_2949_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v_v_2949_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_s_2970_);
lean_dec(v_v_2949_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
lean_ctor_set_tag(v___x_2972_, 0);
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_s_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
v_a_2966_ = v___x_2975_;
goto v___jp_2965_;
}
}
}
case 1:
{
uint8_t v_b_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
v_b_2978_ = lean_ctor_get_uint8(v_v_2949_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v_v_2949_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v_v_2949_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_dec(v_v_2949_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2984_, 0, v_b_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
v_a_2966_ = v___x_2983_;
goto v___jp_2965_;
}
}
}
case 2:
{
lean_object* v_n_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_3000_; 
v_n_2986_ = lean_ctor_get(v_v_2949_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v_v_2949_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2988_ = v_v_2949_;
v_isShared_2989_ = v_isSharedCheck_3000_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_n_2986_);
lean_dec(v_v_2949_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_3000_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v_mantissa_2990_; lean_object* v_exponent_2991_; lean_object* v_natZero_2992_; lean_object* v_intZero_2993_; uint8_t v_isNeg_2994_; 
v_mantissa_2990_ = lean_ctor_get(v_n_2986_, 0);
lean_inc(v_mantissa_2990_);
v_exponent_2991_ = lean_ctor_get(v_n_2986_, 1);
lean_inc(v_exponent_2991_);
lean_dec_ref(v_n_2986_);
v_natZero_2992_ = lean_unsigned_to_nat(0u);
v_intZero_2993_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3);
v_isNeg_2994_ = lean_int_dec_lt(v_mantissa_2990_, v_intZero_2993_);
if (v_isNeg_2994_ == 0)
{
uint8_t v___x_2995_; 
v___x_2995_ = lean_nat_dec_eq(v_exponent_2991_, v_natZero_2992_);
lean_dec(v_exponent_2991_);
if (v___x_2995_ == 0)
{
lean_dec(v_mantissa_2990_);
lean_del_object(v___x_2988_);
lean_dec(v_n_2964_);
lean_dec(v_a_2953_);
lean_dec(v_r_2951_);
goto v___jp_2946_;
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; 
v_a_2996_ = lean_nat_abs(v_mantissa_2990_);
lean_dec(v_mantissa_2990_);
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 0, v_a_2996_);
v___x_2998_ = v___x_2988_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2996_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
v_a_2966_ = v___x_2998_;
goto v___jp_2965_;
}
}
}
else
{
lean_dec(v_exponent_2991_);
lean_dec(v_mantissa_2990_);
lean_del_object(v___x_2988_);
lean_dec(v_n_2964_);
lean_dec(v_a_2953_);
lean_dec(v_r_2951_);
goto v___jp_2946_;
}
}
}
default: 
{
lean_dec(v_n_2964_);
lean_dec(v_a_2953_);
lean_dec(v_r_2951_);
lean_dec(v_v_2949_);
goto v___jp_2946_;
}
}
}
else
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3006_; 
lean_dec(v_n_2964_);
lean_dec(v_a_2953_);
lean_dec(v_r_2951_);
lean_dec(v_v_2949_);
v___x_3001_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__4));
v___x_3002_ = lean_string_append(v___x_3001_, v_k_2948_);
lean_dec(v_k_2948_);
v___x_3003_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_3004_ = lean_string_append(v___x_3002_, v___x_3003_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set_tag(v___x_2955_, 0);
lean_ctor_set(v___x_2955_, 0, v___x_3004_);
v___x_3006_ = v___x_2955_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_3004_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
v___jp_2965_:
{
lean_object* v___x_2967_; 
v___x_2967_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_2964_, v_a_2966_, v_a_2953_);
v_init_2942_ = v___x_2967_;
v_x_2943_ = v_r_2951_;
goto _start;
}
}
else
{
lean_del_object(v___x_2955_);
lean_dec(v_k_2948_);
switch(lean_obj_tag(v_v_2949_))
{
case 3:
{
lean_object* v_s_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
v_s_3008_ = lean_ctor_get(v_v_2949_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v_v_2949_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3010_ = v_v_2949_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_s_3008_);
lean_dec(v_v_2949_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
if (v_isShared_3011_ == 0)
{
lean_ctor_set_tag(v___x_3010_, 0);
v___x_3013_ = v___x_3010_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_s_3008_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
v_a_2958_ = v___x_3013_;
goto v___jp_2957_;
}
}
}
case 1:
{
uint8_t v_b_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
v_b_3016_ = lean_ctor_get_uint8(v_v_2949_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v_v_2949_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v_v_2949_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_dec(v_v_2949_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_3022_, 0, v_b_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
v_a_2958_ = v___x_3021_;
goto v___jp_2957_;
}
}
}
case 2:
{
lean_object* v_n_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3038_; 
v_n_3024_ = lean_ctor_get(v_v_2949_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v_v_2949_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3026_ = v_v_2949_;
v_isShared_3027_ = v_isSharedCheck_3038_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_n_3024_);
lean_dec(v_v_2949_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3038_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v_mantissa_3028_; lean_object* v_exponent_3029_; lean_object* v_natZero_3030_; lean_object* v_intZero_3031_; uint8_t v_isNeg_3032_; 
v_mantissa_3028_ = lean_ctor_get(v_n_3024_, 0);
lean_inc(v_mantissa_3028_);
v_exponent_3029_ = lean_ctor_get(v_n_3024_, 1);
lean_inc(v_exponent_3029_);
lean_dec_ref(v_n_3024_);
v_natZero_3030_ = lean_unsigned_to_nat(0u);
v_intZero_3031_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__3);
v_isNeg_3032_ = lean_int_dec_lt(v_mantissa_3028_, v_intZero_3031_);
if (v_isNeg_3032_ == 0)
{
uint8_t v___x_3033_; 
v___x_3033_ = lean_nat_dec_eq(v_exponent_3029_, v_natZero_3030_);
lean_dec(v_exponent_3029_);
if (v___x_3033_ == 0)
{
lean_dec(v_mantissa_3028_);
lean_del_object(v___x_3026_);
lean_dec(v_a_2953_);
lean_dec(v_r_2951_);
goto v___jp_2944_;
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; 
v_a_3034_ = lean_nat_abs(v_mantissa_3028_);
lean_dec(v_mantissa_3028_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v_a_3034_);
v___x_3036_ = v___x_3026_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3034_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
v_a_2958_ = v___x_3036_;
goto v___jp_2957_;
}
}
}
else
{
lean_dec(v_exponent_3029_);
lean_dec(v_mantissa_3028_);
lean_del_object(v___x_3026_);
lean_dec(v_a_2953_);
lean_dec(v_r_2951_);
goto v___jp_2944_;
}
}
}
default: 
{
lean_dec(v_a_2953_);
lean_dec(v_r_2951_);
lean_dec(v_v_2949_);
goto v___jp_2944_;
}
}
}
v___jp_2957_:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2959_ = lean_box(0);
v___x_2960_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2959_, v_a_2958_, v_a_2953_);
v_init_2942_ = v___x_2960_;
v_x_2943_ = v_r_2951_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3040_; 
v___x_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3040_, 0, v_init_2942_);
return v___x_3040_;
}
v___jp_2944_:
{
lean_object* v___x_2945_; 
v___x_2945_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__1));
return v___x_2945_;
}
v___jp_2946_:
{
lean_object* v___x_2947_; 
v___x_2947_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__1));
return v___x_2947_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8(lean_object* v_x_3042_){
_start:
{
if (lean_obj_tag(v_x_3042_) == 5)
{
lean_object* v_kvPairs_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v_kvPairs_3043_ = lean_ctor_get(v_x_3042_, 0);
lean_inc(v_kvPairs_3043_);
lean_dec_ref_known(v_x_3042_, 1);
v___x_3044_ = lean_box(1);
v___x_3045_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13(v___x_3044_, v_kvPairs_3043_);
return v___x_3045_;
}
else
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3046_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8___closed__0));
v___x_3047_ = lean_unsigned_to_nat(80u);
v___x_3048_ = l_Lean_Json_pretty(v_x_3042_, v___x_3047_);
v___x_3049_ = lean_string_append(v___x_3046_, v___x_3048_);
lean_dec_ref(v___x_3048_);
v___x_3050_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_3051_ = lean_string_append(v___x_3049_, v___x_3050_);
v___x_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3051_);
return v___x_3052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4(lean_object* v_j_3053_, lean_object* v_k_3054_){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = l_Lean_Json_getObjValD(v_j_3053_, v_k_3054_);
v___x_3056_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8(v___x_3055_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3059_ = v___x_3056_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3056_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_a_3057_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
else
{
lean_object* v_a_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3072_; 
v_a_3065_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3067_ = v___x_3056_;
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_a_3065_);
lean_dec(v___x_3056_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
if (v_isShared_3068_ == 0)
{
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_a_3065_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4___boxed(lean_object* v_j_3073_, lean_object* v_k_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4(v_j_3073_, v_k_3074_);
lean_dec_ref(v_k_3074_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__10(size_t v_sz_3076_, size_t v_i_3077_, lean_object* v_bs_3078_){
_start:
{
uint8_t v___x_3079_; 
v___x_3079_ = lean_usize_dec_lt(v_i_3077_, v_sz_3076_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; 
v___x_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3080_, 0, v_bs_3078_);
return v___x_3080_;
}
else
{
lean_object* v_v_3081_; lean_object* v___x_3082_; 
v_v_3081_ = lean_array_uget_borrowed(v_bs_3078_, v_i_3077_);
lean_inc(v_v_3081_);
v___x_3082_ = l_Lean_Plugin_fromJson_x3f(v_v_3081_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
lean_dec_ref(v_bs_3078_);
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_3082_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3082_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3092_; lean_object* v_bs_x27_3093_; size_t v___x_3094_; size_t v___x_3095_; lean_object* v___x_3096_; 
v_a_3091_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_a_3091_);
lean_dec_ref_known(v___x_3082_, 1);
v___x_3092_ = lean_unsigned_to_nat(0u);
v_bs_x27_3093_ = lean_array_uset(v_bs_3078_, v_i_3077_, v___x_3092_);
v___x_3094_ = ((size_t)1ULL);
v___x_3095_ = lean_usize_add(v_i_3077_, v___x_3094_);
v___x_3096_ = lean_array_uset(v_bs_x27_3093_, v_i_3077_, v_a_3091_);
v_i_3077_ = v___x_3095_;
v_bs_3078_ = v___x_3096_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__10___boxed(lean_object* v_sz_3098_, lean_object* v_i_3099_, lean_object* v_bs_3100_){
_start:
{
size_t v_sz_boxed_3101_; size_t v_i_boxed_3102_; lean_object* v_res_3103_; 
v_sz_boxed_3101_ = lean_unbox_usize(v_sz_3098_);
lean_dec(v_sz_3098_);
v_i_boxed_3102_ = lean_unbox_usize(v_i_3099_);
lean_dec(v_i_3099_);
v_res_3103_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__10(v_sz_boxed_3101_, v_i_boxed_3102_, v_bs_3100_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6(lean_object* v_x_3104_){
_start:
{
if (lean_obj_tag(v_x_3104_) == 4)
{
lean_object* v_elems_3105_; size_t v_sz_3106_; size_t v___x_3107_; lean_object* v___x_3108_; 
v_elems_3105_ = lean_ctor_get(v_x_3104_, 0);
lean_inc_ref(v_elems_3105_);
lean_dec_ref_known(v_x_3104_, 1);
v_sz_3106_ = lean_array_size(v_elems_3105_);
v___x_3107_ = ((size_t)0ULL);
v___x_3108_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__10(v_sz_3106_, v___x_3107_, v_elems_3105_);
return v___x_3108_;
}
else
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3109_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0));
v___x_3110_ = lean_unsigned_to_nat(80u);
v___x_3111_ = l_Lean_Json_pretty(v_x_3104_, v___x_3110_);
v___x_3112_ = lean_string_append(v___x_3109_, v___x_3111_);
lean_dec_ref(v___x_3111_);
v___x_3113_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_3114_ = lean_string_append(v___x_3112_, v___x_3113_);
v___x_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3114_);
return v___x_3115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3(lean_object* v_j_3116_, lean_object* v_k_3117_){
_start:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3118_ = l_Lean_Json_getObjValD(v_j_3116_, v_k_3117_);
v___x_3119_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6(v___x_3118_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3___boxed(lean_object* v_j_3120_, lean_object* v_k_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3(v_j_3120_, v_k_3121_);
lean_dec_ref(v_k_3121_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0(lean_object* v_x_3125_){
_start:
{
if (lean_obj_tag(v_x_3125_) == 0)
{
lean_object* v___x_3126_; 
v___x_3126_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0___closed__0));
return v___x_3126_;
}
else
{
lean_object* v___x_3127_; 
v___x_3127_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0(v_x_3125_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
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
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3144_; 
v_a_3136_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3138_ = v___x_3127_;
v_isShared_3139_ = v_isSharedCheck_3144_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3127_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3144_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3140_; lean_object* v___x_3142_; 
v___x_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3140_, 0, v_a_3136_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 0, v___x_3140_);
v___x_3142_ = v___x_3138_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3140_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0(lean_object* v_j_3145_, lean_object* v_k_3146_){
_start:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3147_ = l_Lean_Json_getObjValD(v_j_3145_, v_k_3146_);
v___x_3148_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0(v___x_3147_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0___boxed(lean_object* v_j_3149_, lean_object* v_k_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0(v_j_3149_, v_k_3150_);
lean_dec_ref(v_k_3150_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__7(size_t v_sz_3152_, size_t v_i_3153_, lean_object* v_bs_3154_){
_start:
{
uint8_t v___x_3155_; 
v___x_3155_ = lean_usize_dec_lt(v_i_3153_, v_sz_3152_);
if (v___x_3155_ == 0)
{
lean_object* v___x_3156_; 
v___x_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3156_, 0, v_bs_3154_);
return v___x_3156_;
}
else
{
lean_object* v_v_3157_; lean_object* v___x_3158_; 
v_v_3157_ = lean_array_uget_borrowed(v_bs_3154_, v_i_3153_);
lean_inc(v_v_3157_);
v___x_3158_ = l_Lean_Json_getStr_x3f(v_v_3157_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
lean_dec_ref(v_bs_3154_);
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___x_3158_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3158_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3159_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3168_; lean_object* v_bs_x27_3169_; size_t v___x_3170_; size_t v___x_3171_; lean_object* v___x_3172_; 
v_a_3167_ = lean_ctor_get(v___x_3158_, 0);
lean_inc(v_a_3167_);
lean_dec_ref_known(v___x_3158_, 1);
v___x_3168_ = lean_unsigned_to_nat(0u);
v_bs_x27_3169_ = lean_array_uset(v_bs_3154_, v_i_3153_, v___x_3168_);
v___x_3170_ = ((size_t)1ULL);
v___x_3171_ = lean_usize_add(v_i_3153_, v___x_3170_);
v___x_3172_ = lean_array_uset(v_bs_x27_3169_, v_i_3153_, v_a_3167_);
v_i_3153_ = v___x_3171_;
v_bs_3154_ = v___x_3172_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__7___boxed(lean_object* v_sz_3174_, lean_object* v_i_3175_, lean_object* v_bs_3176_){
_start:
{
size_t v_sz_boxed_3177_; size_t v_i_boxed_3178_; lean_object* v_res_3179_; 
v_sz_boxed_3177_ = lean_unbox_usize(v_sz_3174_);
lean_dec(v_sz_3174_);
v_i_boxed_3178_ = lean_unbox_usize(v_i_3175_);
lean_dec(v_i_3175_);
v_res_3179_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__7(v_sz_boxed_3177_, v_i_boxed_3178_, v_bs_3176_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4(lean_object* v_x_3180_){
_start:
{
if (lean_obj_tag(v_x_3180_) == 4)
{
lean_object* v_elems_3181_; size_t v_sz_3182_; size_t v___x_3183_; lean_object* v___x_3184_; 
v_elems_3181_ = lean_ctor_get(v_x_3180_, 0);
lean_inc_ref(v_elems_3181_);
lean_dec_ref_known(v_x_3180_, 1);
v_sz_3182_ = lean_array_size(v_elems_3181_);
v___x_3183_ = ((size_t)0ULL);
v___x_3184_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__7(v_sz_3182_, v___x_3183_, v_elems_3181_);
return v___x_3184_;
}
else
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3185_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0));
v___x_3186_ = lean_unsigned_to_nat(80u);
v___x_3187_ = l_Lean_Json_pretty(v_x_3180_, v___x_3186_);
v___x_3188_ = lean_string_append(v___x_3185_, v___x_3187_);
lean_dec_ref(v___x_3187_);
v___x_3189_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_3190_ = lean_string_append(v___x_3188_, v___x_3189_);
v___x_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
return v___x_3191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3_spec__7(size_t v_sz_3192_, size_t v_i_3193_, lean_object* v_bs_3194_){
_start:
{
uint8_t v___x_3195_; 
v___x_3195_ = lean_usize_dec_lt(v_i_3193_, v_sz_3192_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; 
v___x_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3196_, 0, v_bs_3194_);
return v___x_3196_;
}
else
{
lean_object* v_v_3197_; lean_object* v___x_3198_; 
v_v_3197_ = lean_array_uget_borrowed(v_bs_3194_, v_i_3193_);
lean_inc(v_v_3197_);
v___x_3198_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4(v_v_3197_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
lean_dec_ref(v_bs_3194_);
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___x_3198_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3198_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
else
{
lean_object* v_a_3207_; lean_object* v___x_3208_; lean_object* v_bs_x27_3209_; size_t v___x_3210_; size_t v___x_3211_; lean_object* v___x_3212_; 
v_a_3207_ = lean_ctor_get(v___x_3198_, 0);
lean_inc(v_a_3207_);
lean_dec_ref_known(v___x_3198_, 1);
v___x_3208_ = lean_unsigned_to_nat(0u);
v_bs_x27_3209_ = lean_array_uset(v_bs_3194_, v_i_3193_, v___x_3208_);
v___x_3210_ = ((size_t)1ULL);
v___x_3211_ = lean_usize_add(v_i_3193_, v___x_3210_);
v___x_3212_ = lean_array_uset(v_bs_x27_3209_, v_i_3193_, v_a_3207_);
v_i_3193_ = v___x_3211_;
v_bs_3194_ = v___x_3212_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3_spec__7___boxed(lean_object* v_sz_3214_, lean_object* v_i_3215_, lean_object* v_bs_3216_){
_start:
{
size_t v_sz_boxed_3217_; size_t v_i_boxed_3218_; lean_object* v_res_3219_; 
v_sz_boxed_3217_ = lean_unbox_usize(v_sz_3214_);
lean_dec(v_sz_3214_);
v_i_boxed_3218_ = lean_unbox_usize(v_i_3215_);
lean_dec(v_i_3215_);
v_res_3219_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3_spec__7(v_sz_boxed_3217_, v_i_boxed_3218_, v_bs_3216_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3(lean_object* v_x_3220_){
_start:
{
if (lean_obj_tag(v_x_3220_) == 4)
{
lean_object* v_elems_3221_; size_t v_sz_3222_; size_t v___x_3223_; lean_object* v___x_3224_; 
v_elems_3221_ = lean_ctor_get(v_x_3220_, 0);
lean_inc_ref(v_elems_3221_);
lean_dec_ref_known(v_x_3220_, 1);
v_sz_3222_ = lean_array_size(v_elems_3221_);
v___x_3223_ = ((size_t)0ULL);
v___x_3224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3_spec__7(v_sz_3222_, v___x_3223_, v_elems_3221_);
return v___x_3224_;
}
else
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3225_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0));
v___x_3226_ = lean_unsigned_to_nat(80u);
v___x_3227_ = l_Lean_Json_pretty(v_x_3220_, v___x_3226_);
v___x_3228_ = lean_string_append(v___x_3225_, v___x_3227_);
lean_dec_ref(v___x_3227_);
v___x_3229_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_3230_ = lean_string_append(v___x_3228_, v___x_3229_);
v___x_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
return v___x_3231_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__4(lean_object* v_init_3232_, lean_object* v_x_3233_){
_start:
{
if (lean_obj_tag(v_x_3233_) == 0)
{
lean_object* v_k_3234_; lean_object* v_v_3235_; lean_object* v_l_3236_; lean_object* v_r_3237_; lean_object* v___x_3238_; 
v_k_3234_ = lean_ctor_get(v_x_3233_, 1);
lean_inc(v_k_3234_);
v_v_3235_ = lean_ctor_get(v_x_3233_, 2);
lean_inc(v_v_3235_);
v_l_3236_ = lean_ctor_get(v_x_3233_, 3);
lean_inc(v_l_3236_);
v_r_3237_ = lean_ctor_get(v_x_3233_, 4);
lean_inc(v_r_3237_);
lean_dec_ref_known(v_x_3233_, 5);
v___x_3238_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__4(v_init_3232_, v_l_3236_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_dec(v_r_3237_);
lean_dec(v_v_3235_);
lean_dec(v_k_3234_);
return v___x_3238_;
}
else
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3279_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3241_ = v___x_3238_;
v_isShared_3242_ = v_isSharedCheck_3279_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3238_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3279_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3243_; uint8_t v___x_3244_; 
v___x_3243_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__2));
v___x_3244_ = lean_string_dec_eq(v_k_3234_, v___x_3243_);
if (v___x_3244_ == 0)
{
lean_object* v_n_3245_; uint8_t v___x_3246_; 
lean_inc(v_k_3234_);
v_n_3245_ = l_String_toName(v_k_3234_);
v___x_3246_ = l_Lean_Name_isAnonymous(v_n_3245_);
if (v___x_3246_ == 0)
{
lean_object* v___x_3247_; 
lean_del_object(v___x_3241_);
lean_dec(v_k_3234_);
v___x_3247_ = l_Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3(v_v_3235_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec(v_n_3245_);
lean_dec(v_a_3239_);
lean_dec(v_r_3237_);
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3247_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3247_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
else
{
lean_object* v_a_3256_; lean_object* v___x_3257_; 
v_a_3256_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_a_3256_);
lean_dec_ref_known(v___x_3247_, 1);
v___x_3257_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_3245_, v_a_3256_, v_a_3239_);
v_init_3232_ = v___x_3257_;
v_x_3233_ = v_r_3237_;
goto _start;
}
}
else
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3264_; 
lean_dec(v_n_3245_);
lean_dec(v_a_3239_);
lean_dec(v_r_3237_);
lean_dec(v_v_3235_);
v___x_3259_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__13___closed__4));
v___x_3260_ = lean_string_append(v___x_3259_, v_k_3234_);
lean_dec(v_k_3234_);
v___x_3261_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_3262_ = lean_string_append(v___x_3260_, v___x_3261_);
if (v_isShared_3242_ == 0)
{
lean_ctor_set_tag(v___x_3241_, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3262_);
v___x_3264_ = v___x_3241_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3262_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
else
{
lean_object* v___x_3266_; 
lean_del_object(v___x_3241_);
lean_dec(v_k_3234_);
v___x_3266_ = l_Lean_Array_fromJson_x3f___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3(v_v_3235_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3274_; 
lean_dec(v_a_3239_);
lean_dec(v_r_3237_);
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3269_ = v___x_3266_;
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3266_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
if (v_isShared_3270_ == 0)
{
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3267_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v_a_3275_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3266_, 1);
v___x_3276_ = lean_box(0);
v___x_3277_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_3276_, v_a_3275_, v_a_3239_);
v_init_3232_ = v___x_3277_;
v_x_3233_ = v_r_3237_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_3280_; 
v___x_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3280_, 0, v_init_3232_);
return v___x_3280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2(lean_object* v_x_3281_){
_start:
{
if (lean_obj_tag(v_x_3281_) == 5)
{
lean_object* v_kvPairs_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v_kvPairs_3282_ = lean_ctor_get(v_x_3281_, 0);
lean_inc(v_kvPairs_3282_);
lean_dec_ref_known(v_x_3281_, 1);
v___x_3283_ = lean_box(1);
v___x_3284_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__4(v___x_3283_, v_kvPairs_3282_);
return v___x_3284_;
}
else
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3285_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8___closed__0));
v___x_3286_ = lean_unsigned_to_nat(80u);
v___x_3287_ = l_Lean_Json_pretty(v_x_3281_, v___x_3286_);
v___x_3288_ = lean_string_append(v___x_3285_, v___x_3287_);
lean_dec_ref(v___x_3287_);
v___x_3289_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_3290_ = lean_string_append(v___x_3288_, v___x_3289_);
v___x_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3290_);
return v___x_3291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1(lean_object* v_j_3292_, lean_object* v_k_3293_){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3294_ = l_Lean_Json_getObjValD(v_j_3292_, v_k_3293_);
v___x_3295_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2(v___x_3294_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1___boxed(lean_object* v_j_3296_, lean_object* v_k_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1(v_j_3296_, v_k_3297_);
lean_dec_ref(v_k_3297_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2(lean_object* v_j_3299_, lean_object* v_k_3300_){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = l_Lean_Json_getObjValD(v_j_3299_, v_k_3300_);
v___x_3302_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4(v___x_3301_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2___boxed(lean_object* v_j_3303_, lean_object* v_k_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2(v_j_3303_, v_k_3304_);
lean_dec_ref(v_k_3304_);
return v_res_3305_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3310_ = 1;
v___x_3311_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__1));
v___x_3312_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3311_, v___x_3310_);
return v___x_3312_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3313_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__4));
v___x_3314_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__2, &l_Lean_instFromJsonModuleSetup_fromJson___closed__2_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__2);
v___x_3315_ = lean_string_append(v___x_3314_, v___x_3313_);
return v___x_3315_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__5(void){
_start:
{
uint8_t v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3318_ = 1;
v___x_3319_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__4));
v___x_3320_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3319_, v___x_3318_);
return v___x_3320_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__6(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3321_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__5, &l_Lean_instFromJsonModuleSetup_fromJson___closed__5_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__5);
v___x_3322_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3323_ = lean_string_append(v___x_3322_, v___x_3321_);
return v___x_3323_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3324_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3325_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__6, &l_Lean_instFromJsonModuleSetup_fromJson___closed__6_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__6);
v___x_3326_ = lean_string_append(v___x_3325_, v___x_3324_);
return v___x_3326_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__9(void){
_start:
{
uint8_t v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3329_ = 1;
v___x_3330_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__8));
v___x_3331_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3330_, v___x_3329_);
return v___x_3331_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3332_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__9, &l_Lean_instFromJsonModuleSetup_fromJson___closed__9_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__9);
v___x_3333_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3334_ = lean_string_append(v___x_3333_, v___x_3332_);
return v___x_3334_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__11(void){
_start:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3335_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3336_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__10, &l_Lean_instFromJsonModuleSetup_fromJson___closed__10_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__10);
v___x_3337_ = lean_string_append(v___x_3336_, v___x_3335_);
return v___x_3337_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3338_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__9, &l_Lean_instFromJsonModuleHeader_fromJson___closed__9_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__9);
v___x_3339_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3340_ = lean_string_append(v___x_3339_, v___x_3338_);
return v___x_3340_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__13(void){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3341_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3342_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__12, &l_Lean_instFromJsonModuleSetup_fromJson___closed__12_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__12);
v___x_3343_ = lean_string_append(v___x_3342_, v___x_3341_);
return v___x_3343_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__15(void){
_start:
{
uint8_t v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3346_ = 1;
v___x_3347_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__14));
v___x_3348_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3347_, v___x_3346_);
return v___x_3348_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__16(void){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3349_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__15, &l_Lean_instFromJsonModuleSetup_fromJson___closed__15_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__15);
v___x_3350_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3351_ = lean_string_append(v___x_3350_, v___x_3349_);
return v___x_3351_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__17(void){
_start:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3352_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3353_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__16, &l_Lean_instFromJsonModuleSetup_fromJson___closed__16_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__16);
v___x_3354_ = lean_string_append(v___x_3353_, v___x_3352_);
return v___x_3354_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__19(void){
_start:
{
uint8_t v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3357_ = 1;
v___x_3358_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__18));
v___x_3359_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3358_, v___x_3357_);
return v___x_3359_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__20(void){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3360_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__19, &l_Lean_instFromJsonModuleSetup_fromJson___closed__19_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__19);
v___x_3361_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3362_ = lean_string_append(v___x_3361_, v___x_3360_);
return v___x_3362_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__21(void){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3363_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3364_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__20, &l_Lean_instFromJsonModuleSetup_fromJson___closed__20_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__20);
v___x_3365_ = lean_string_append(v___x_3364_, v___x_3363_);
return v___x_3365_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__23(void){
_start:
{
uint8_t v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3368_ = 1;
v___x_3369_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__22));
v___x_3370_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3369_, v___x_3368_);
return v___x_3370_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__24(void){
_start:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3371_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__23, &l_Lean_instFromJsonModuleSetup_fromJson___closed__23_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__23);
v___x_3372_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3373_ = lean_string_append(v___x_3372_, v___x_3371_);
return v___x_3373_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__25(void){
_start:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3374_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3375_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__24, &l_Lean_instFromJsonModuleSetup_fromJson___closed__24_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__24);
v___x_3376_ = lean_string_append(v___x_3375_, v___x_3374_);
return v___x_3376_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__27(void){
_start:
{
uint8_t v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3379_ = 1;
v___x_3380_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__26));
v___x_3381_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3380_, v___x_3379_);
return v___x_3381_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__28(void){
_start:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3382_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__27, &l_Lean_instFromJsonModuleSetup_fromJson___closed__27_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__27);
v___x_3383_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3384_ = lean_string_append(v___x_3383_, v___x_3382_);
return v___x_3384_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__29(void){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3385_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3386_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__28, &l_Lean_instFromJsonModuleSetup_fromJson___closed__28_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__28);
v___x_3387_ = lean_string_append(v___x_3386_, v___x_3385_);
return v___x_3387_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__31(void){
_start:
{
uint8_t v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3390_ = 1;
v___x_3391_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__30));
v___x_3392_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3391_, v___x_3390_);
return v___x_3392_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__32(void){
_start:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3393_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__31, &l_Lean_instFromJsonModuleSetup_fromJson___closed__31_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__31);
v___x_3394_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3395_ = lean_string_append(v___x_3394_, v___x_3393_);
return v___x_3395_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__33(void){
_start:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3396_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3397_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__32, &l_Lean_instFromJsonModuleSetup_fromJson___closed__32_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__32);
v___x_3398_ = lean_string_append(v___x_3397_, v___x_3396_);
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonModuleSetup_fromJson(lean_object* v_json_3399_){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__0));
lean_inc(v_json_3399_);
v___x_3401_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__0(v_json_3399_, v___x_3400_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3411_; 
lean_dec(v_json_3399_);
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3404_ = v___x_3401_;
v_isShared_3405_ = v_isSharedCheck_3411_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3401_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3411_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3409_; 
v___x_3406_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__7, &l_Lean_instFromJsonModuleSetup_fromJson___closed__7_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__7);
v___x_3407_ = lean_string_append(v___x_3406_, v_a_3402_);
lean_dec(v_a_3402_);
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 0, v___x_3407_);
v___x_3409_ = v___x_3404_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3407_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
else
{
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v_a_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3419_; 
lean_dec(v_json_3399_);
v_a_3412_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v___x_3401_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3401_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
lean_ctor_set_tag(v___x_3414_, 0);
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3412_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
else
{
lean_object* v_a_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v_a_3420_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_a_3420_);
lean_dec_ref_known(v___x_3401_, 1);
v___x_3421_ = ((lean_object*)(l_Lean_instToJsonModuleSetup_toJson___closed__0));
lean_inc(v_json_3399_);
v___x_3422_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1(v_json_3399_, v___x_3421_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3432_; 
lean_dec(v_a_3420_);
lean_dec(v_json_3399_);
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3425_ = v___x_3422_;
v_isShared_3426_ = v_isSharedCheck_3432_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3422_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3432_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3430_; 
v___x_3427_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__11, &l_Lean_instFromJsonModuleSetup_fromJson___closed__11_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__11);
v___x_3428_ = lean_string_append(v___x_3427_, v_a_3423_);
lean_dec(v_a_3423_);
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 0, v___x_3428_);
v___x_3430_ = v___x_3425_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3428_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
else
{
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3440_; 
lean_dec(v_a_3420_);
lean_dec(v_json_3399_);
v_a_3433_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3435_ = v___x_3422_;
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3422_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3438_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set_tag(v___x_3435_, 0);
v___x_3438_ = v___x_3435_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3433_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
else
{
lean_object* v_a_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v_a_3441_ = lean_ctor_get(v___x_3422_, 0);
lean_inc(v_a_3441_);
lean_dec_ref_known(v___x_3422_, 1);
v___x_3442_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__5));
lean_inc(v_json_3399_);
v___x_3443_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(v_json_3399_, v___x_3442_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3453_; 
lean_dec(v_a_3441_);
lean_dec(v_a_3420_);
lean_dec(v_json_3399_);
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3446_ = v___x_3443_;
v_isShared_3447_ = v_isSharedCheck_3453_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3443_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3453_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3451_; 
v___x_3448_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__13, &l_Lean_instFromJsonModuleSetup_fromJson___closed__13_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__13);
v___x_3449_ = lean_string_append(v___x_3448_, v_a_3444_);
lean_dec(v_a_3444_);
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 0, v___x_3449_);
v___x_3451_ = v___x_3446_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3449_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
else
{
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3461_; 
lean_dec(v_a_3441_);
lean_dec(v_a_3420_);
lean_dec(v_json_3399_);
v_a_3454_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3456_ = v___x_3443_;
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3443_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3459_; 
if (v_isShared_3457_ == 0)
{
lean_ctor_set_tag(v___x_3456_, 0);
v___x_3459_ = v___x_3456_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_a_3454_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
}
else
{
lean_object* v_a_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
v_a_3462_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_a_3462_);
lean_dec_ref_known(v___x_3443_, 1);
v___x_3463_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__0));
lean_inc(v_json_3399_);
v___x_3464_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0(v_json_3399_, v___x_3463_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3474_; 
lean_dec(v_a_3462_);
lean_dec(v_a_3441_);
lean_dec(v_a_3420_);
lean_dec(v_json_3399_);
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3467_ = v___x_3464_;
v_isShared_3468_ = v_isSharedCheck_3474_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3474_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3472_; 
v___x_3469_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__17, &l_Lean_instFromJsonModuleSetup_fromJson___closed__17_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__17);
v___x_3470_ = lean_string_append(v___x_3469_, v_a_3465_);
lean_dec(v_a_3465_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v___x_3470_);
v___x_3472_ = v___x_3467_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3470_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
else
{
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
lean_dec(v_a_3462_);
lean_dec(v_a_3441_);
lean_dec(v_a_3420_);
lean_dec(v_json_3399_);
v_a_3475_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3464_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3464_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
lean_ctor_set_tag(v___x_3477_, 0);
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v_a_3483_ = lean_ctor_get(v___x_3464_, 0);
lean_inc(v_a_3483_);
lean_dec_ref_known(v___x_3464_, 1);
v___x_3484_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__8));
lean_inc(v_json_3399_);
v___x_3485_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1(v_json_3399_, v___x_3484_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3495_; 
lean_dec(v_a_3483_);
lean_dec(v_a_3462_);
lean_dec(v_a_3441_);
lean_dec(v_a_3420_);
lean_dec(v_json_3399_);
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3488_ = v___x_3485_;
v_isShared_3489_ = v_isSharedCheck_3495_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3485_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3495_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3493_; 
v___x_3490_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__21, &l_Lean_instFromJsonModuleSetup_fromJson___closed__21_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__21);
v___x_3491_ = lean_string_append(v___x_3490_, v_a_3486_);
lean_dec(v_a_3486_);
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 0, v___x_3491_);
v___x_3493_ = v___x_3488_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3491_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
else
{
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
lean_dec(v_a_3483_);
lean_dec(v_a_3462_);
lean_dec(v_a_3441_);
lean_dec(v_a_3420_);
lean_dec(v_json_3399_);
v_a_3496_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3485_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3485_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
lean_ctor_set_tag(v___x_3498_, 0);
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v_a_3504_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___x_3485_, 1);
v___x_3505_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__12));
lean_inc(v_json_3399_);
v___x_3506_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2(v_json_3399_, v___x_3505_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3516_; 
lean_dec(v_a_3504_);
lean_dec(v_a_3483_);
lean_dec(v_a_3462_);
lean_dec(v_a_3441_);
lean_dec(v_a_3420_);
lean_dec(v_json_3399_);
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3509_ = v___x_3506_;
v_isShared_3510_ = v_isSharedCheck_3516_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3506_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3516_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3514_; 
v___x_3511_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__25, &l_Lean_instFromJsonModuleSetup_fromJson___closed__25_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__25);
v___x_3512_ = lean_string_append(v___x_3511_, v_a_3507_);
lean_dec(v_a_3507_);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 0, v___x_3512_);
v___x_3514_ = v___x_3509_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3512_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
else
{
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
lean_dec(v_a_3504_);
lean_dec(v_a_3483_);
lean_dec(v_a_3462_);
lean_dec(v_a_3441_);
lean_dec(v_a_3420_);
lean_dec(v_json_3399_);
v_a_3517_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3519_ = v___x_3506_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3506_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
lean_ctor_set_tag(v___x_3519_, 0);
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3517_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
else
{
lean_object* v_a_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v_a_3525_ = lean_ctor_get(v___x_3506_, 0);
lean_inc(v_a_3525_);
lean_dec_ref_known(v___x_3506_, 1);
v___x_3526_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__14));
lean_inc(v_json_3399_);
v___x_3527_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3(v_json_3399_, v___x_3526_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3537_; 
lean_dec(v_a_3525_);
lean_dec(v_a_3504_);
lean_dec(v_a_3483_);
lean_dec(v_a_3462_);
lean_dec(v_a_3441_);
lean_dec(v_a_3420_);
lean_dec(v_json_3399_);
v_a_3528_ = lean_ctor_get(v___x_3527_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3530_ = v___x_3527_;
v_isShared_3531_ = v_isSharedCheck_3537_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3527_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3537_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3535_; 
v___x_3532_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__29, &l_Lean_instFromJsonModuleSetup_fromJson___closed__29_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__29);
v___x_3533_ = lean_string_append(v___x_3532_, v_a_3528_);
lean_dec(v_a_3528_);
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 0, v___x_3533_);
v___x_3535_ = v___x_3530_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3533_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
else
{
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
lean_dec(v_a_3525_);
lean_dec(v_a_3504_);
lean_dec(v_a_3483_);
lean_dec(v_a_3462_);
lean_dec(v_a_3441_);
lean_dec(v_a_3420_);
lean_dec(v_json_3399_);
v_a_3538_ = lean_ctor_get(v___x_3527_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3527_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3527_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
lean_ctor_set_tag(v___x_3540_, 0);
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v_a_3546_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_a_3546_);
lean_dec_ref_known(v___x_3527_, 1);
v___x_3547_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__16));
v___x_3548_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4(v_json_3399_, v___x_3547_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3558_; 
lean_dec(v_a_3546_);
lean_dec(v_a_3525_);
lean_dec(v_a_3504_);
lean_dec(v_a_3483_);
lean_dec(v_a_3462_);
lean_dec(v_a_3441_);
lean_dec(v_a_3420_);
v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3551_ = v___x_3548_;
v_isShared_3552_ = v_isSharedCheck_3558_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3548_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3558_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3556_; 
v___x_3553_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__33, &l_Lean_instFromJsonModuleSetup_fromJson___closed__33_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__33);
v___x_3554_ = lean_string_append(v___x_3553_, v_a_3549_);
lean_dec(v_a_3549_);
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 0, v___x_3554_);
v___x_3556_ = v___x_3551_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
else
{
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_dec(v_a_3546_);
lean_dec(v_a_3525_);
lean_dec(v_a_3504_);
lean_dec(v_a_3483_);
lean_dec(v_a_3462_);
lean_dec(v_a_3441_);
lean_dec(v_a_3420_);
v_a_3559_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3548_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3548_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
lean_ctor_set_tag(v___x_3561_, 0);
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3576_; 
v_a_3567_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3569_ = v___x_3548_;
v_isShared_3570_ = v_isSharedCheck_3576_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3548_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3576_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3571_; uint8_t v___x_3572_; lean_object* v___x_3574_; 
v___x_3571_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3571_, 0, v_a_3420_);
lean_ctor_set(v___x_3571_, 1, v_a_3441_);
lean_ctor_set(v___x_3571_, 2, v_a_3483_);
lean_ctor_set(v___x_3571_, 3, v_a_3504_);
lean_ctor_set(v___x_3571_, 4, v_a_3525_);
lean_ctor_set(v___x_3571_, 5, v_a_3546_);
lean_ctor_set(v___x_3571_, 6, v_a_3567_);
v___x_3572_ = lean_unbox(v_a_3462_);
lean_dec(v_a_3462_);
lean_ctor_set_uint8(v___x_3571_, sizeof(void*)*7, v___x_3572_);
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 0, v___x_3571_);
v___x_3574_ = v___x_3569_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3571_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleSetup_load(lean_object* v_path_3580_){
_start:
{
lean_object* v___x_3582_; 
v___x_3582_ = l_IO_FS_readFile(v_path_3580_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3611_; 
v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3585_ = v___x_3582_;
v_isShared_3586_ = v_isSharedCheck_3611_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3582_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3611_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v_a_3588_; lean_object* v___x_3598_; 
v___x_3598_ = l_Lean_Json_parse(v_a_3583_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v___x_3598_, 1);
v_a_3588_ = v_a_3599_;
goto v___jp_3587_;
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3601_; 
v_a_3600_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3600_);
lean_dec_ref_known(v___x_3598_, 1);
v___x_3601_ = l_Lean_instFromJsonModuleSetup_fromJson(v_a_3600_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
lean_inc(v_a_3602_);
lean_dec_ref_known(v___x_3601_, 1);
v_a_3588_ = v_a_3602_;
goto v___jp_3587_;
}
else
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
lean_del_object(v___x_3585_);
v_a_3603_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3601_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3601_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
lean_ctor_set_tag(v___x_3605_, 0);
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3603_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
v___jp_3587_:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3596_; 
v___x_3589_ = ((lean_object*)(l_Lean_ModuleSetup_load___closed__0));
v___x_3590_ = lean_string_append(v___x_3589_, v_path_3580_);
v___x_3591_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3592_ = lean_string_append(v___x_3590_, v___x_3591_);
v___x_3593_ = lean_string_append(v___x_3592_, v_a_3588_);
lean_dec_ref(v_a_3588_);
v___x_3594_ = lean_mk_io_user_error(v___x_3593_);
if (v_isShared_3586_ == 0)
{
lean_ctor_set_tag(v___x_3585_, 1);
lean_ctor_set(v___x_3585_, 0, v___x_3594_);
v___x_3596_ = v___x_3585_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3594_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
v_a_3612_ = lean_ctor_get(v___x_3582_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3582_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3582_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleSetup_load___boxed(lean_object* v_path_3620_, lean_object* v_a_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lean_ModuleSetup_load(v_path_3620_);
lean_dec_ref(v_path_3620_);
return v_res_3622_;
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
