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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_instReprLeanOptions_repr___redArg(lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_instFromJsonFilePath___lam__0(lean_object*);
lean_object* l_Array_fromJson_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instToJsonFilePath___lam__0(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_toJson___redArg(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_instHashableImport_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_instHashableImport_hash___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IRPhases_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_IRPhases_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonModuleHeader_toJson(lean_object*);
static const lean_closure_object l_Lean_instToJsonModuleHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonModuleHeader_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonModuleHeader___closed__0 = (const lean_object*)&l_Lean_instToJsonModuleHeader___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonModuleHeader = (const lean_object*)&l_Lean_instToJsonModuleHeader___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0(lean_object*);
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
static const lean_string_object l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "FilePath.mk "};
static const lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__0 = (const lean_object*)&l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__0_value;
static const lean_ctor_object l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__0_value)}};
static const lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__1 = (const lean_object*)&l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_instReprImportArtifacts_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
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
static const lean_closure_object l_Lean_instToJsonImportArtifacts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonImportArtifacts___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_instToJsonImportArtifacts___closed__0_value)} };
static const lean_object* l_Lean_instToJsonImportArtifacts___closed__1 = (const lean_object*)&l_Lean_instToJsonImportArtifacts___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonImportArtifacts = (const lean_object*)&l_Lean_instToJsonImportArtifacts___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instFromJsonImportArtifacts___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instFromJsonImportArtifacts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonFilePath___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonImportArtifacts___closed__0 = (const lean_object*)&l_Lean_instFromJsonImportArtifacts___closed__0_value;
static const lean_closure_object l_Lean_instFromJsonImportArtifacts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonImportArtifacts___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_instFromJsonImportArtifacts___closed__0_value)} };
static const lean_object* l_Lean_instFromJsonImportArtifacts___closed__1 = (const lean_object*)&l_Lean_instFromJsonImportArtifacts___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonImportArtifacts = (const lean_object*)&l_Lean_instFromJsonImportArtifacts___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_size___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_olean_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_olean_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_ir_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_ir_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanServer_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanServer_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanPrivate_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanPrivate_x3f___boxed(lean_object*);
static const lean_array_object l_Lean_ImportArtifacts_oleanParts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_ImportArtifacts_oleanParts___closed__0 = (const lean_object*)&l_Lean_ImportArtifacts_oleanParts___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanParts(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanParts___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ir\?"};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__15 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__15_value;
static const lean_ctor_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__15_value)}};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__16 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__16_value;
static lean_once_cell_t l_Lean_instReprModuleArtifacts_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__17;
static const lean_string_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "c\?"};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__18 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__18_value;
static const lean_ctor_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__18_value)}};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__19 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__19_value;
static lean_once_cell_t l_Lean_instReprModuleArtifacts_repr___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__20;
static const lean_string_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bc\?"};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__21 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__21_value;
static const lean_ctor_object l_Lean_instReprModuleArtifacts_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__21_value)}};
static const lean_object* l_Lean_instReprModuleArtifacts_repr___redArg___closed__22 = (const lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__22_value;
LEAN_EXPORT lean_object* l_Lean_instReprModuleArtifacts_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprModuleArtifacts_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprModuleArtifacts_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprModuleArtifacts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprModuleArtifacts_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprModuleArtifacts___closed__0 = (const lean_object*)&l_Lean_instReprModuleArtifacts___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprModuleArtifacts = (const lean_object*)&l_Lean_instReprModuleArtifacts___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedModuleArtifacts_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_string_object l_Lean_instToJsonModuleArtifacts_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l_Lean_instToJsonModuleArtifacts_toJson___closed__5 = (const lean_object*)&l_Lean_instToJsonModuleArtifacts_toJson___closed__5_value;
static const lean_string_object l_Lean_instToJsonModuleArtifacts_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "c"};
static const lean_object* l_Lean_instToJsonModuleArtifacts_toJson___closed__6 = (const lean_object*)&l_Lean_instToJsonModuleArtifacts_toJson___closed__6_value;
static const lean_string_object l_Lean_instToJsonModuleArtifacts_toJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bc"};
static const lean_object* l_Lean_instToJsonModuleArtifacts_toJson___closed__7 = (const lean_object*)&l_Lean_instToJsonModuleArtifacts_toJson___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonModuleArtifacts_toJson(lean_object*);
static const lean_closure_object l_Lean_instToJsonModuleArtifacts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonModuleArtifacts_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonModuleArtifacts___closed__0 = (const lean_object*)&l_Lean_instToJsonModuleArtifacts___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonModuleArtifacts = (const lean_object*)&l_Lean_instToJsonModuleArtifacts___closed__0_value;
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0(lean_object*);
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
static const lean_ctor_object l_Lean_instFromJsonModuleArtifacts_fromJson___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(107, 198, 234, 26, 172, 111, 119, 17)}};
static const lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__24 = (const lean_object*)&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__24_value;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27;
static const lean_ctor_object l_Lean_instFromJsonModuleArtifacts_fromJson___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__18_value),LEAN_SCALAR_PTR_LITERAL(31, 145, 40, 88, 138, 45, 124, 142)}};
static const lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__28 = (const lean_object*)&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__28_value;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31;
static const lean_ctor_object l_Lean_instFromJsonModuleArtifacts_fromJson___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprModuleArtifacts_repr___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(38, 234, 246, 30, 222, 18, 116, 36)}};
static const lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__32 = (const lean_object*)&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__32_value;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34;
static lean_once_cell_t l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35;
LEAN_EXPORT lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson(lean_object*);
static const lean_closure_object l_Lean_instFromJsonModuleArtifacts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonModuleArtifacts_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonModuleArtifacts___closed__0 = (const lean_object*)&l_Lean_instFromJsonModuleArtifacts___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonModuleArtifacts = (const lean_object*)&l_Lean_instFromJsonModuleArtifacts___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_ModuleArtifacts_oleanParts(lean_object*);
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
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1_spec__1(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2___redArg(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Data.DTreeMap.Internal.Balancing"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__6_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__7;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__8;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonModuleSetup_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__8_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4(lean_object*);
static const lean_string_object l_Lean_instToJsonModuleSetup_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "package"};
static const lean_object* l_Lean_instToJsonModuleSetup_toJson___closed__0 = (const lean_object*)&l_Lean_instToJsonModuleSetup_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonModuleSetup_toJson(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__8(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instToJsonModuleSetup___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonModuleSetup_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonModuleSetup___closed__0 = (const lean_object*)&l_Lean_instToJsonModuleSetup___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonModuleSetup = (const lean_object*)&l_Lean_instToJsonModuleSetup___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "invalid LeanOptionValue type"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__0_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__0_value)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[anonymous]"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__3;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "expected a `Name`, got '"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__4 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__4_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12(lean_object*, lean_object*);
static const lean_string_object l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "expected a `NameMap`, got '"};
static const lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8___closed__0 = (const lean_object*)&l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3(lean_object*, lean_object*);
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
lean_dec_ref(v_a_109_);
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
lean_dec_ref(v___x_224_);
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
lean_dec_ref(v___x_245_);
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
lean_dec_ref(v___x_266_);
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
if (v_importAll_323_ == 0)
{
if (v_importAll_327_ == 0)
{
v___y_333_ = v___x_334_;
goto v___jp_332_;
}
else
{
return v_importAll_323_;
}
}
else
{
v___y_333_ = v_importAll_327_;
goto v___jp_332_;
}
}
v___jp_330_:
{
if (v_isMeta_325_ == 0)
{
if (v_isMeta_329_ == 0)
{
return v___y_331_;
}
else
{
return v_isMeta_325_;
}
}
else
{
return v_isMeta_329_;
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
if (v_isExported_324_ == 0)
{
if (v_isExported_328_ == 0)
{
v___y_331_ = v___y_333_;
goto v___jp_330_;
}
else
{
return v_isExported_324_;
}
}
else
{
if (v_isExported_328_ == 0)
{
return v_isExported_328_;
}
else
{
v___y_331_ = v_isExported_328_;
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
static uint64_t _init_l_Lean_instHashableImport_hash___closed__0(void){
_start:
{
lean_object* v___x_341_; uint64_t v___x_342_; 
v___x_341_ = lean_unsigned_to_nat(1723u);
v___x_342_ = lean_uint64_of_nat(v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableImport_hash(lean_object* v_x_343_){
_start:
{
lean_object* v_module_344_; uint8_t v_importAll_345_; uint8_t v_isExported_346_; uint8_t v_isMeta_347_; uint64_t v___y_349_; uint64_t v___y_350_; uint64_t v___y_357_; uint64_t v___y_358_; uint64_t v___x_362_; uint64_t v___y_364_; 
v_module_344_ = lean_ctor_get(v_x_343_, 0);
v_importAll_345_ = lean_ctor_get_uint8(v_x_343_, sizeof(void*)*1);
v_isExported_346_ = lean_ctor_get_uint8(v_x_343_, sizeof(void*)*1 + 1);
v_isMeta_347_ = lean_ctor_get_uint8(v_x_343_, sizeof(void*)*1 + 2);
v___x_362_ = 0ULL;
if (lean_obj_tag(v_module_344_) == 0)
{
uint64_t v___x_368_; 
v___x_368_ = lean_uint64_once(&l_Lean_instHashableImport_hash___closed__0, &l_Lean_instHashableImport_hash___closed__0_once, _init_l_Lean_instHashableImport_hash___closed__0);
v___y_364_ = v___x_368_;
goto v___jp_363_;
}
else
{
uint64_t v_hash_369_; 
v_hash_369_ = lean_ctor_get_uint64(v_module_344_, sizeof(void*)*2);
v___y_364_ = v_hash_369_;
goto v___jp_363_;
}
v___jp_348_:
{
uint64_t v___x_351_; 
v___x_351_ = lean_uint64_mix_hash(v___y_349_, v___y_350_);
if (v_isMeta_347_ == 0)
{
uint64_t v___x_352_; uint64_t v___x_353_; 
v___x_352_ = 13ULL;
v___x_353_ = lean_uint64_mix_hash(v___x_351_, v___x_352_);
return v___x_353_;
}
else
{
uint64_t v___x_354_; uint64_t v___x_355_; 
v___x_354_ = 11ULL;
v___x_355_ = lean_uint64_mix_hash(v___x_351_, v___x_354_);
return v___x_355_;
}
}
v___jp_356_:
{
uint64_t v___x_359_; 
v___x_359_ = lean_uint64_mix_hash(v___y_357_, v___y_358_);
if (v_isExported_346_ == 0)
{
uint64_t v___x_360_; 
v___x_360_ = 13ULL;
v___y_349_ = v___x_359_;
v___y_350_ = v___x_360_;
goto v___jp_348_;
}
else
{
uint64_t v___x_361_; 
v___x_361_ = 11ULL;
v___y_349_ = v___x_359_;
v___y_350_ = v___x_361_;
goto v___jp_348_;
}
}
v___jp_363_:
{
uint64_t v___x_365_; 
v___x_365_ = lean_uint64_mix_hash(v___x_362_, v___y_364_);
if (v_importAll_345_ == 0)
{
uint64_t v___x_366_; 
v___x_366_ = 13ULL;
v___y_357_ = v___x_365_;
v___y_358_ = v___x_366_;
goto v___jp_356_;
}
else
{
uint64_t v___x_367_; 
v___x_367_ = 11ULL;
v___y_357_ = v___x_365_;
v___y_358_ = v___x_367_;
goto v___jp_356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableImport_hash___boxed(lean_object* v_x_370_){
_start:
{
uint64_t v_res_371_; lean_object* v_r_372_; 
v_res_371_ = l_Lean_instHashableImport_hash(v_x_370_);
lean_dec_ref(v_x_370_);
v_r_372_ = lean_box_uint64(v_res_371_);
return v_r_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Idbg_idbgClientLoop___boxed(lean_object* v_00_u03b1_381_, lean_object* v_inst_00___x40_Lean_Setup_1068012781____hygCtx___hyg_382_, lean_object* v_siteId_383_, lean_object* v_imports_384_, lean_object* v_apply_385_, lean_object* v_a_00___x40___internal___hyg_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = lean_idbg_client_loop(v_siteId_383_, v_imports_384_, v_apply_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeNameImport___lam__0(lean_object* v_x_388_){
_start:
{
uint8_t v___x_389_; uint8_t v___x_390_; lean_object* v___x_391_; 
v___x_389_ = 0;
v___x_390_ = 1;
v___x_391_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_391_, 0, v_x_388_);
lean_ctor_set_uint8(v___x_391_, sizeof(void*)*1, v___x_389_);
lean_ctor_set_uint8(v___x_391_, sizeof(void*)*1 + 1, v___x_390_);
lean_ctor_set_uint8(v___x_391_, sizeof(void*)*1 + 2, v___x_389_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringImport___lam__0(lean_object* v_imp_399_){
_start:
{
lean_object* v_module_400_; uint8_t v_importAll_401_; uint8_t v_isExported_402_; uint8_t v_isMeta_403_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_420_; 
v_module_400_ = lean_ctor_get(v_imp_399_, 0);
lean_inc(v_module_400_);
v_importAll_401_ = lean_ctor_get_uint8(v_imp_399_, sizeof(void*)*1);
v_isExported_402_ = lean_ctor_get_uint8(v_imp_399_, sizeof(void*)*1 + 1);
v_isMeta_403_ = lean_ctor_get_uint8(v_imp_399_, sizeof(void*)*1 + 2);
lean_dec_ref(v_imp_399_);
if (v_isExported_402_ == 0)
{
lean_object* v___x_423_; 
v___x_423_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__1));
v___y_420_ = v___x_423_;
goto v___jp_419_;
}
else
{
lean_object* v___x_424_; 
v___x_424_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__4));
v___y_420_ = v___x_424_;
goto v___jp_419_;
}
v___jp_404_:
{
lean_object* v___x_407_; uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_407_ = lean_string_append(v___y_405_, v___y_406_);
v___x_408_ = 1;
v___x_409_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_400_, v___x_408_);
v___x_410_ = lean_string_append(v___x_407_, v___x_409_);
lean_dec_ref(v___x_409_);
return v___x_410_;
}
v___jp_411_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
lean_inc_ref(v___y_412_);
v___x_414_ = lean_string_append(v___y_412_, v___y_413_);
v___x_415_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__0));
v___x_416_ = lean_string_append(v___x_414_, v___x_415_);
if (v_importAll_401_ == 0)
{
lean_object* v___x_417_; 
v___x_417_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__1));
v___y_405_ = v___x_416_;
v___y_406_ = v___x_417_;
goto v___jp_404_;
}
else
{
lean_object* v___x_418_; 
v___x_418_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__2));
v___y_405_ = v___x_416_;
v___y_406_ = v___x_418_;
goto v___jp_404_;
}
}
v___jp_419_:
{
if (v_isMeta_403_ == 0)
{
lean_object* v___x_421_; 
v___x_421_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__1));
v___y_412_ = v___y_420_;
v___y_413_ = v___x_421_;
goto v___jp_411_;
}
else
{
lean_object* v___x_422_; 
v___x_422_ = ((lean_object*)(l_Lean_instToStringImport___lam__0___closed__3));
v___y_412_ = v___y_420_;
v___y_413_ = v___x_422_;
goto v___jp_411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorIdx(uint8_t v_x_427_){
_start:
{
switch(v_x_427_)
{
case 0:
{
lean_object* v___x_428_; 
v___x_428_ = lean_unsigned_to_nat(0u);
return v___x_428_;
}
case 1:
{
lean_object* v___x_429_; 
v___x_429_ = lean_unsigned_to_nat(1u);
return v___x_429_;
}
default: 
{
lean_object* v___x_430_; 
v___x_430_ = lean_unsigned_to_nat(2u);
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorIdx___boxed(lean_object* v_x_431_){
_start:
{
uint8_t v_x_boxed_432_; lean_object* v_res_433_; 
v_x_boxed_432_ = lean_unbox(v_x_431_);
v_res_433_ = l_Lean_IRPhases_ctorIdx(v_x_boxed_432_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_toCtorIdx(uint8_t v_x_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_IRPhases_ctorIdx(v_x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_toCtorIdx___boxed(lean_object* v_x_436_){
_start:
{
uint8_t v_x_4__boxed_437_; lean_object* v_res_438_; 
v_x_4__boxed_437_ = lean_unbox(v_x_436_);
v_res_438_ = l_Lean_IRPhases_toCtorIdx(v_x_4__boxed_437_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorElim___redArg(lean_object* v_k_439_){
_start:
{
lean_inc(v_k_439_);
return v_k_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorElim___redArg___boxed(lean_object* v_k_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_IRPhases_ctorElim___redArg(v_k_440_);
lean_dec(v_k_440_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorElim(lean_object* v_motive_442_, lean_object* v_ctorIdx_443_, uint8_t v_t_444_, lean_object* v_h_445_, lean_object* v_k_446_){
_start:
{
lean_inc(v_k_446_);
return v_k_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_ctorElim___boxed(lean_object* v_motive_447_, lean_object* v_ctorIdx_448_, lean_object* v_t_449_, lean_object* v_h_450_, lean_object* v_k_451_){
_start:
{
uint8_t v_t_boxed_452_; lean_object* v_res_453_; 
v_t_boxed_452_ = lean_unbox(v_t_449_);
v_res_453_ = l_Lean_IRPhases_ctorElim(v_motive_447_, v_ctorIdx_448_, v_t_boxed_452_, v_h_450_, v_k_451_);
lean_dec(v_k_451_);
lean_dec(v_ctorIdx_448_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_runtime_elim___redArg(lean_object* v_runtime_454_){
_start:
{
lean_inc(v_runtime_454_);
return v_runtime_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_runtime_elim___redArg___boxed(lean_object* v_runtime_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_IRPhases_runtime_elim___redArg(v_runtime_455_);
lean_dec(v_runtime_455_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_runtime_elim(lean_object* v_motive_457_, uint8_t v_t_458_, lean_object* v_h_459_, lean_object* v_runtime_460_){
_start:
{
lean_inc(v_runtime_460_);
return v_runtime_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_runtime_elim___boxed(lean_object* v_motive_461_, lean_object* v_t_462_, lean_object* v_h_463_, lean_object* v_runtime_464_){
_start:
{
uint8_t v_t_boxed_465_; lean_object* v_res_466_; 
v_t_boxed_465_ = lean_unbox(v_t_462_);
v_res_466_ = l_Lean_IRPhases_runtime_elim(v_motive_461_, v_t_boxed_465_, v_h_463_, v_runtime_464_);
lean_dec(v_runtime_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_comptime_elim___redArg(lean_object* v_comptime_467_){
_start:
{
lean_inc(v_comptime_467_);
return v_comptime_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_comptime_elim___redArg___boxed(lean_object* v_comptime_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_IRPhases_comptime_elim___redArg(v_comptime_468_);
lean_dec(v_comptime_468_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_comptime_elim(lean_object* v_motive_470_, uint8_t v_t_471_, lean_object* v_h_472_, lean_object* v_comptime_473_){
_start:
{
lean_inc(v_comptime_473_);
return v_comptime_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_comptime_elim___boxed(lean_object* v_motive_474_, lean_object* v_t_475_, lean_object* v_h_476_, lean_object* v_comptime_477_){
_start:
{
uint8_t v_t_boxed_478_; lean_object* v_res_479_; 
v_t_boxed_478_ = lean_unbox(v_t_475_);
v_res_479_ = l_Lean_IRPhases_comptime_elim(v_motive_474_, v_t_boxed_478_, v_h_476_, v_comptime_477_);
lean_dec(v_comptime_477_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_all_elim___redArg(lean_object* v_all_480_){
_start:
{
lean_inc(v_all_480_);
return v_all_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_all_elim___redArg___boxed(lean_object* v_all_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_IRPhases_all_elim___redArg(v_all_481_);
lean_dec(v_all_481_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_all_elim(lean_object* v_motive_483_, uint8_t v_t_484_, lean_object* v_h_485_, lean_object* v_all_486_){
_start:
{
lean_inc(v_all_486_);
return v_all_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_IRPhases_all_elim___boxed(lean_object* v_motive_487_, lean_object* v_t_488_, lean_object* v_h_489_, lean_object* v_all_490_){
_start:
{
uint8_t v_t_boxed_491_; lean_object* v_res_492_; 
v_t_boxed_491_ = lean_unbox(v_t_488_);
v_res_492_ = l_Lean_IRPhases_all_elim(v_motive_487_, v_t_boxed_491_, v_h_489_, v_all_490_);
lean_dec(v_all_490_);
return v_res_492_;
}
}
static uint8_t _init_l_Lean_instInhabitedIRPhases_default(void){
_start:
{
uint8_t v___x_493_; 
v___x_493_ = 0;
return v___x_493_;
}
}
static uint8_t _init_l_Lean_instInhabitedIRPhases(void){
_start:
{
uint8_t v___x_494_; 
v___x_494_ = 0;
return v___x_494_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqIRPhases_beq(uint8_t v_x_495_, uint8_t v_y_496_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_497_ = l_Lean_IRPhases_ctorIdx(v_x_495_);
v___x_498_ = l_Lean_IRPhases_ctorIdx(v_y_496_);
v___x_499_ = lean_nat_dec_eq(v___x_497_, v___x_498_);
lean_dec(v___x_498_);
lean_dec(v___x_497_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqIRPhases_beq___boxed(lean_object* v_x_500_, lean_object* v_y_501_){
_start:
{
uint8_t v_x_17__boxed_502_; uint8_t v_y_18__boxed_503_; uint8_t v_res_504_; lean_object* v_r_505_; 
v_x_17__boxed_502_ = lean_unbox(v_x_500_);
v_y_18__boxed_503_ = lean_unbox(v_y_501_);
v_res_504_ = l_Lean_instBEqIRPhases_beq(v_x_17__boxed_502_, v_y_18__boxed_503_);
v_r_505_ = lean_box(v_res_504_);
return v_r_505_;
}
}
static lean_object* _init_l_Lean_instReprIRPhases_repr___closed__6(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_unsigned_to_nat(2u);
v___x_518_ = lean_nat_to_int(v___x_517_);
return v___x_518_;
}
}
static lean_object* _init_l_Lean_instReprIRPhases_repr___closed__7(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_unsigned_to_nat(1u);
v___x_520_ = lean_nat_to_int(v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprIRPhases_repr(uint8_t v_x_521_, lean_object* v_prec_522_){
_start:
{
lean_object* v___y_524_; lean_object* v___y_531_; lean_object* v___y_538_; 
switch(v_x_521_)
{
case 0:
{
lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_544_ = lean_unsigned_to_nat(1024u);
v___x_545_ = lean_nat_dec_le(v___x_544_, v_prec_522_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
v___x_546_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__6, &l_Lean_instReprIRPhases_repr___closed__6_once, _init_l_Lean_instReprIRPhases_repr___closed__6);
v___y_524_ = v___x_546_;
goto v___jp_523_;
}
else
{
lean_object* v___x_547_; 
v___x_547_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__7, &l_Lean_instReprIRPhases_repr___closed__7_once, _init_l_Lean_instReprIRPhases_repr___closed__7);
v___y_524_ = v___x_547_;
goto v___jp_523_;
}
}
case 1:
{
lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_548_ = lean_unsigned_to_nat(1024u);
v___x_549_ = lean_nat_dec_le(v___x_548_, v_prec_522_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; 
v___x_550_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__6, &l_Lean_instReprIRPhases_repr___closed__6_once, _init_l_Lean_instReprIRPhases_repr___closed__6);
v___y_531_ = v___x_550_;
goto v___jp_530_;
}
else
{
lean_object* v___x_551_; 
v___x_551_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__7, &l_Lean_instReprIRPhases_repr___closed__7_once, _init_l_Lean_instReprIRPhases_repr___closed__7);
v___y_531_ = v___x_551_;
goto v___jp_530_;
}
}
default: 
{
lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_552_ = lean_unsigned_to_nat(1024u);
v___x_553_ = lean_nat_dec_le(v___x_552_, v_prec_522_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; 
v___x_554_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__6, &l_Lean_instReprIRPhases_repr___closed__6_once, _init_l_Lean_instReprIRPhases_repr___closed__6);
v___y_538_ = v___x_554_;
goto v___jp_537_;
}
else
{
lean_object* v___x_555_; 
v___x_555_ = lean_obj_once(&l_Lean_instReprIRPhases_repr___closed__7, &l_Lean_instReprIRPhases_repr___closed__7_once, _init_l_Lean_instReprIRPhases_repr___closed__7);
v___y_538_ = v___x_555_;
goto v___jp_537_;
}
}
}
v___jp_523_:
{
lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_525_ = ((lean_object*)(l_Lean_instReprIRPhases_repr___closed__1));
lean_inc(v___y_524_);
v___x_526_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_526_, 0, v___y_524_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = 0;
v___x_528_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_528_, 0, v___x_526_);
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*1, v___x_527_);
v___x_529_ = l_Repr_addAppParen(v___x_528_, v_prec_522_);
return v___x_529_;
}
v___jp_530_:
{
lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_532_ = ((lean_object*)(l_Lean_instReprIRPhases_repr___closed__3));
lean_inc(v___y_531_);
v___x_533_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_533_, 0, v___y_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = 0;
v___x_535_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set_uint8(v___x_535_, sizeof(void*)*1, v___x_534_);
v___x_536_ = l_Repr_addAppParen(v___x_535_, v_prec_522_);
return v___x_536_;
}
v___jp_537_:
{
lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_539_ = ((lean_object*)(l_Lean_instReprIRPhases_repr___closed__5));
lean_inc(v___y_538_);
v___x_540_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_540_, 0, v___y_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = 0;
v___x_542_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*1, v___x_541_);
v___x_543_ = l_Repr_addAppParen(v___x_542_, v_prec_522_);
return v___x_543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprIRPhases_repr___boxed(lean_object* v_x_556_, lean_object* v_prec_557_){
_start:
{
uint8_t v_x_177__boxed_558_; lean_object* v_res_559_; 
v_x_177__boxed_558_ = lean_unbox(v_x_556_);
v_res_559_ = l_Lean_instReprIRPhases_repr(v_x_177__boxed_558_, v_prec_557_);
lean_dec(v_prec_557_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_562_, lean_object* v_x_563_, lean_object* v_x_564_){
_start:
{
if (lean_obj_tag(v_x_564_) == 0)
{
lean_dec(v_x_562_);
return v_x_563_;
}
else
{
lean_object* v_head_565_; lean_object* v_tail_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_576_; 
v_head_565_ = lean_ctor_get(v_x_564_, 0);
v_tail_566_ = lean_ctor_get(v_x_564_, 1);
v_isSharedCheck_576_ = !lean_is_exclusive(v_x_564_);
if (v_isSharedCheck_576_ == 0)
{
v___x_568_ = v_x_564_;
v_isShared_569_ = v_isSharedCheck_576_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_tail_566_);
lean_inc(v_head_565_);
lean_dec(v_x_564_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_576_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
lean_inc(v_x_562_);
if (v_isShared_569_ == 0)
{
lean_ctor_set_tag(v___x_568_, 5);
lean_ctor_set(v___x_568_, 1, v_x_562_);
lean_ctor_set(v___x_568_, 0, v_x_563_);
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_x_563_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_x_562_);
v___x_571_ = v_reuseFailAlloc_575_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = l_Lean_instReprImport_repr___redArg(v_head_565_);
v___x_573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_571_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v_x_563_ = v___x_573_;
v_x_564_ = v_tail_566_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0_spec__1(lean_object* v_x_577_, lean_object* v_x_578_, lean_object* v_x_579_){
_start:
{
if (lean_obj_tag(v_x_579_) == 0)
{
lean_dec(v_x_577_);
return v_x_578_;
}
else
{
lean_object* v_head_580_; lean_object* v_tail_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_591_; 
v_head_580_ = lean_ctor_get(v_x_579_, 0);
v_tail_581_ = lean_ctor_get(v_x_579_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v_x_579_);
if (v_isSharedCheck_591_ == 0)
{
v___x_583_ = v_x_579_;
v_isShared_584_ = v_isSharedCheck_591_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_tail_581_);
lean_inc(v_head_580_);
lean_dec(v_x_579_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_591_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
lean_inc(v_x_577_);
if (v_isShared_584_ == 0)
{
lean_ctor_set_tag(v___x_583_, 5);
lean_ctor_set(v___x_583_, 1, v_x_577_);
lean_ctor_set(v___x_583_, 0, v_x_578_);
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_x_578_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_x_577_);
v___x_586_ = v_reuseFailAlloc_590_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_587_ = l_Lean_instReprImport_repr___redArg(v_head_580_);
v___x_588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0_spec__1_spec__2(v_x_577_, v___x_588_, v_tail_581_);
return v___x_589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0(lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
if (lean_obj_tag(v_x_592_) == 0)
{
lean_object* v___x_594_; 
lean_dec(v_x_593_);
v___x_594_ = lean_box(0);
return v___x_594_;
}
else
{
lean_object* v_tail_595_; 
v_tail_595_ = lean_ctor_get(v_x_592_, 1);
if (lean_obj_tag(v_tail_595_) == 0)
{
lean_object* v_head_596_; lean_object* v___x_597_; 
lean_dec(v_x_593_);
v_head_596_ = lean_ctor_get(v_x_592_, 0);
lean_inc(v_head_596_);
lean_dec_ref(v_x_592_);
v___x_597_ = l_Lean_instReprImport_repr___redArg(v_head_596_);
return v___x_597_;
}
else
{
lean_object* v_head_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
lean_inc(v_tail_595_);
v_head_598_ = lean_ctor_get(v_x_592_, 0);
lean_inc(v_head_598_);
lean_dec_ref(v_x_592_);
v___x_599_ = l_Lean_instReprImport_repr___redArg(v_head_598_);
v___x_600_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0_spec__1(v_x_593_, v___x_599_, v_tail_595_);
return v___x_600_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__0));
v___x_607_ = lean_string_length(v___x_606_);
return v___x_607_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_obj_once(&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3, &l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3);
v___x_609_ = lean_nat_to_int(v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0(lean_object* v_xs_617_){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_618_ = lean_array_get_size(v_xs_617_);
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = lean_nat_dec_eq(v___x_618_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_621_ = lean_array_to_list(v_xs_617_);
v___x_622_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_623_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0(v___x_621_, v___x_622_);
v___x_624_ = lean_obj_once(&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4);
v___x_625_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5));
v___x_626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v___x_623_);
v___x_627_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6));
v___x_628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_626_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_624_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v___x_630_ = l_Std_Format_fill(v___x_629_);
return v___x_630_;
}
else
{
lean_object* v___x_631_; 
lean_dec_ref(v_xs_617_);
v___x_631_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8));
return v___x_631_;
}
}
}
static lean_object* _init_l_Lean_instReprModuleHeader_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_unsigned_to_nat(11u);
v___x_642_ = lean_nat_to_int(v___x_641_);
return v___x_642_;
}
}
static lean_object* _init_l_Lean_instReprModuleHeader_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_unsigned_to_nat(12u);
v___x_647_ = lean_nat_to_int(v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleHeader_repr___redArg(lean_object* v_x_648_){
_start:
{
lean_object* v_imports_649_; uint8_t v_isModule_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_683_; 
v_imports_649_ = lean_ctor_get(v_x_648_, 0);
v_isModule_650_ = lean_ctor_get_uint8(v_x_648_, sizeof(void*)*1);
v_isSharedCheck_683_ = !lean_is_exclusive(v_x_648_);
if (v_isSharedCheck_683_ == 0)
{
v___x_652_ = v_x_648_;
v_isShared_653_ = v_isSharedCheck_683_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_imports_649_);
lean_dec(v_x_648_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_683_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; lean_object* v___x_661_; 
v___x_654_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__5));
v___x_655_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__3));
v___x_656_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__4, &l_Lean_instReprModuleHeader_repr___redArg___closed__4_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__4);
v___x_657_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0(v_imports_649_);
v___x_658_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_656_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = 0;
if (v_isShared_653_ == 0)
{
lean_ctor_set_tag(v___x_652_, 6);
lean_ctor_set(v___x_652_, 0, v___x_658_);
v___x_661_ = v___x_652_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_658_);
v___x_661_ = v_reuseFailAlloc_682_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
lean_ctor_set_uint8(v___x_661_, sizeof(void*)*1, v___x_659_);
v___x_662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_655_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__9));
v___x_664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_662_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = lean_box(1);
v___x_666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_664_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__6));
v___x_668_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_666_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
lean_ctor_set(v___x_669_, 1, v___x_654_);
v___x_670_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__7, &l_Lean_instReprModuleHeader_repr___redArg___closed__7_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__7);
v___x_671_ = l_Bool_repr___redArg(v_isModule_650_);
v___x_672_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_670_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_ctor_set_uint8(v___x_673_, sizeof(void*)*1, v___x_659_);
v___x_674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_669_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__20, &l_Lean_instReprImport_repr___redArg___closed__20_once, _init_l_Lean_instReprImport_repr___redArg___closed__20);
v___x_676_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__21));
v___x_677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
lean_ctor_set(v___x_677_, 1, v___x_674_);
v___x_678_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__22));
v___x_679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_677_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_675_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set_uint8(v___x_681_, sizeof(void*)*1, v___x_659_);
return v___x_681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleHeader_repr(lean_object* v_x_684_, lean_object* v_prec_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_instReprModuleHeader_repr___redArg(v_x_684_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleHeader_repr___boxed(lean_object* v_x_687_, lean_object* v_prec_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_instReprModuleHeader_repr(v_x_687_, v_prec_688_);
lean_dec(v_prec_688_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0(size_t v_sz_699_, size_t v_i_700_, lean_object* v_bs_701_){
_start:
{
uint8_t v___x_702_; 
v___x_702_ = lean_usize_dec_lt(v_i_700_, v_sz_699_);
if (v___x_702_ == 0)
{
return v_bs_701_;
}
else
{
lean_object* v_v_703_; lean_object* v___x_704_; lean_object* v_bs_x27_705_; lean_object* v___x_706_; size_t v___x_707_; size_t v___x_708_; lean_object* v___x_709_; 
v_v_703_ = lean_array_uget(v_bs_701_, v_i_700_);
v___x_704_ = lean_unsigned_to_nat(0u);
v_bs_x27_705_ = lean_array_uset(v_bs_701_, v_i_700_, v___x_704_);
v___x_706_ = l_Lean_instToJsonImport_toJson(v_v_703_);
v___x_707_ = ((size_t)1ULL);
v___x_708_ = lean_usize_add(v_i_700_, v___x_707_);
v___x_709_ = lean_array_uset(v_bs_x27_705_, v_i_700_, v___x_706_);
v_i_700_ = v___x_708_;
v_bs_701_ = v___x_709_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0___boxed(lean_object* v_sz_711_, lean_object* v_i_712_, lean_object* v_bs_713_){
_start:
{
size_t v_sz_boxed_714_; size_t v_i_boxed_715_; lean_object* v_res_716_; 
v_sz_boxed_714_ = lean_unbox_usize(v_sz_711_);
lean_dec(v_sz_711_);
v_i_boxed_715_ = lean_unbox_usize(v_i_712_);
lean_dec(v_i_712_);
v_res_716_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0(v_sz_boxed_714_, v_i_boxed_715_, v_bs_713_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0(lean_object* v_a_717_){
_start:
{
size_t v_sz_718_; size_t v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v_sz_718_ = lean_array_size(v_a_717_);
v___x_719_ = ((size_t)0ULL);
v___x_720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0(v_sz_718_, v___x_719_, v_a_717_);
v___x_721_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonModuleHeader_toJson(lean_object* v_x_722_){
_start:
{
lean_object* v_imports_723_; uint8_t v_isModule_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_imports_723_ = lean_ctor_get(v_x_722_, 0);
lean_inc_ref(v_imports_723_);
v_isModule_724_ = lean_ctor_get_uint8(v_x_722_, sizeof(void*)*1);
lean_dec_ref(v_x_722_);
v___x_725_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__0));
v___x_726_ = l_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0(v_imports_723_);
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = lean_box(0);
v___x_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__5));
v___x_731_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_731_, 0, v_isModule_724_);
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_730_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v___x_728_);
v___x_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set(v___x_734_, 1, v___x_728_);
v___x_735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_729_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = ((lean_object*)(l_Lean_instToJsonImport_toJson___closed__0));
v___x_737_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(v___x_735_, v___x_736_);
v___x_738_ = l_Lean_Json_mkObj(v___x_737_);
lean_dec(v___x_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1(size_t v_sz_741_, size_t v_i_742_, lean_object* v_bs_743_){
_start:
{
uint8_t v___x_744_; 
v___x_744_ = lean_usize_dec_lt(v_i_742_, v_sz_741_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; 
v___x_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_745_, 0, v_bs_743_);
return v___x_745_;
}
else
{
lean_object* v_v_746_; lean_object* v___x_747_; 
v_v_746_ = lean_array_uget_borrowed(v_bs_743_, v_i_742_);
lean_inc(v_v_746_);
v___x_747_ = l_Lean_instFromJsonImport_fromJson(v_v_746_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec_ref(v_bs_743_);
v_a_748_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_747_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_747_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_757_; lean_object* v_bs_x27_758_; size_t v___x_759_; size_t v___x_760_; lean_object* v___x_761_; 
v_a_756_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_756_);
lean_dec_ref(v___x_747_);
v___x_757_ = lean_unsigned_to_nat(0u);
v_bs_x27_758_ = lean_array_uset(v_bs_743_, v_i_742_, v___x_757_);
v___x_759_ = ((size_t)1ULL);
v___x_760_ = lean_usize_add(v_i_742_, v___x_759_);
v___x_761_ = lean_array_uset(v_bs_x27_758_, v_i_742_, v_a_756_);
v_i_742_ = v___x_760_;
v_bs_743_ = v___x_761_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_763_, lean_object* v_i_764_, lean_object* v_bs_765_){
_start:
{
size_t v_sz_boxed_766_; size_t v_i_boxed_767_; lean_object* v_res_768_; 
v_sz_boxed_766_ = lean_unbox_usize(v_sz_763_);
lean_dec(v_sz_763_);
v_i_boxed_767_ = lean_unbox_usize(v_i_764_);
lean_dec(v_i_764_);
v_res_768_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_766_, v_i_boxed_767_, v_bs_765_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0(lean_object* v_x_771_){
_start:
{
if (lean_obj_tag(v_x_771_) == 4)
{
lean_object* v_elems_772_; size_t v_sz_773_; size_t v___x_774_; lean_object* v___x_775_; 
v_elems_772_ = lean_ctor_get(v_x_771_, 0);
lean_inc_ref(v_elems_772_);
lean_dec_ref(v_x_771_);
v_sz_773_ = lean_array_size(v_elems_772_);
v___x_774_ = ((size_t)0ULL);
v___x_775_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1(v_sz_773_, v___x_774_, v_elems_772_);
return v___x_775_;
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_776_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0));
v___x_777_ = lean_unsigned_to_nat(80u);
v___x_778_ = l_Lean_Json_pretty(v_x_771_, v___x_777_);
v___x_779_ = lean_string_append(v___x_776_, v___x_778_);
lean_dec_ref(v___x_778_);
v___x_780_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_781_ = lean_string_append(v___x_779_, v___x_780_);
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
return v___x_782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0(lean_object* v_j_783_, lean_object* v_k_784_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = l_Lean_Json_getObjValD(v_j_783_, v_k_784_);
v___x_786_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0(v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0___boxed(lean_object* v_j_787_, lean_object* v_k_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0(v_j_787_, v_k_788_);
lean_dec_ref(v_k_788_);
return v_res_789_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__2(void){
_start:
{
uint8_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_794_ = 1;
v___x_795_ = ((lean_object*)(l_Lean_instFromJsonModuleHeader_fromJson___closed__1));
v___x_796_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_795_, v___x_794_);
return v___x_796_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__3(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_797_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__4));
v___x_798_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__2, &l_Lean_instFromJsonModuleHeader_fromJson___closed__2_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__2);
v___x_799_ = lean_string_append(v___x_798_, v___x_797_);
return v___x_799_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__5(void){
_start:
{
uint8_t v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_802_ = 1;
v___x_803_ = ((lean_object*)(l_Lean_instFromJsonModuleHeader_fromJson___closed__4));
v___x_804_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_803_, v___x_802_);
return v___x_804_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__6(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_805_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__5, &l_Lean_instFromJsonModuleHeader_fromJson___closed__5_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__5);
v___x_806_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__3, &l_Lean_instFromJsonModuleHeader_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__3);
v___x_807_ = lean_string_append(v___x_806_, v___x_805_);
return v___x_807_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__7(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_808_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_809_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__6, &l_Lean_instFromJsonModuleHeader_fromJson___closed__6_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__6);
v___x_810_ = lean_string_append(v___x_809_, v___x_808_);
return v___x_810_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__9(void){
_start:
{
uint8_t v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_813_ = 1;
v___x_814_ = ((lean_object*)(l_Lean_instFromJsonModuleHeader_fromJson___closed__8));
v___x_815_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_814_, v___x_813_);
return v___x_815_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__10(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_816_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__9, &l_Lean_instFromJsonModuleHeader_fromJson___closed__9_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__9);
v___x_817_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__3, &l_Lean_instFromJsonModuleHeader_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__3);
v___x_818_ = lean_string_append(v___x_817_, v___x_816_);
return v___x_818_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__11(void){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_819_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_820_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__10, &l_Lean_instFromJsonModuleHeader_fromJson___closed__10_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__10);
v___x_821_ = lean_string_append(v___x_820_, v___x_819_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonModuleHeader_fromJson(lean_object* v_json_822_){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__0));
lean_inc(v_json_822_);
v___x_824_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0(v_json_822_, v___x_823_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_834_; 
lean_dec(v_json_822_);
v_a_825_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_834_ == 0)
{
v___x_827_ = v___x_824_;
v_isShared_828_ = v_isSharedCheck_834_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_824_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_834_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_832_; 
v___x_829_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__7, &l_Lean_instFromJsonModuleHeader_fromJson___closed__7_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__7);
v___x_830_ = lean_string_append(v___x_829_, v_a_825_);
lean_dec(v_a_825_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v___x_830_);
v___x_832_ = v___x_827_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
else
{
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec(v_json_822_);
v_a_835_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_824_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_824_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
lean_ctor_set_tag(v___x_837_, 0);
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v_a_843_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_a_843_);
lean_dec_ref(v___x_824_);
v___x_844_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__5));
v___x_845_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(v_json_822_, v___x_844_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_855_; 
lean_dec(v_a_843_);
v_a_846_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_855_ == 0)
{
v___x_848_ = v___x_845_;
v_isShared_849_ = v_isSharedCheck_855_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_845_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_855_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_850_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__11, &l_Lean_instFromJsonModuleHeader_fromJson___closed__11_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__11);
v___x_851_ = lean_string_append(v___x_850_, v_a_846_);
lean_dec(v_a_846_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_851_);
v___x_853_ = v___x_848_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
else
{
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
lean_dec(v_a_843_);
v_a_856_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_845_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_845_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set_tag(v___x_858_, 0);
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_873_; 
v_a_864_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_873_ == 0)
{
v___x_866_ = v___x_845_;
v_isShared_867_ = v_isSharedCheck_873_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_845_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_873_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; uint8_t v___x_869_; lean_object* v___x_871_; 
v___x_868_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_868_, 0, v_a_843_);
v___x_869_ = lean_unbox(v_a_864_);
lean_dec(v_a_864_);
lean_ctor_set_uint8(v___x_868_, sizeof(void*)*1, v___x_869_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_868_);
v___x_871_ = v___x_866_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_868_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_879_, lean_object* v_x_880_, lean_object* v_x_881_){
_start:
{
if (lean_obj_tag(v_x_881_) == 0)
{
lean_dec(v_x_879_);
return v_x_880_;
}
else
{
lean_object* v_head_882_; lean_object* v_tail_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_898_; 
v_head_882_ = lean_ctor_get(v_x_881_, 0);
v_tail_883_ = lean_ctor_get(v_x_881_, 1);
v_isSharedCheck_898_ = !lean_is_exclusive(v_x_881_);
if (v_isSharedCheck_898_ == 0)
{
v___x_885_ = v_x_881_;
v_isShared_886_ = v_isSharedCheck_898_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_tail_883_);
lean_inc(v_head_882_);
lean_dec(v_x_881_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_898_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
lean_inc(v_x_879_);
if (v_isShared_886_ == 0)
{
lean_ctor_set_tag(v___x_885_, 5);
lean_ctor_set(v___x_885_, 1, v_x_879_);
lean_ctor_set(v___x_885_, 0, v_x_880_);
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_x_880_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_x_879_);
v___x_888_ = v_reuseFailAlloc_897_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_889_ = lean_unsigned_to_nat(0u);
v___x_890_ = ((lean_object*)(l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__1));
v___x_891_ = l_String_quote(v_head_882_);
v___x_892_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
v___x_893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_890_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = l_Repr_addAppParen(v___x_893_, v___x_889_);
v___x_895_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_888_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v_x_880_ = v___x_895_;
v_x_881_ = v_tail_883_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1(lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v_x_901_){
_start:
{
if (lean_obj_tag(v_x_901_) == 0)
{
lean_dec(v_x_899_);
return v_x_900_;
}
else
{
lean_object* v_head_902_; lean_object* v_tail_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_918_; 
v_head_902_ = lean_ctor_get(v_x_901_, 0);
v_tail_903_ = lean_ctor_get(v_x_901_, 1);
v_isSharedCheck_918_ = !lean_is_exclusive(v_x_901_);
if (v_isSharedCheck_918_ == 0)
{
v___x_905_ = v_x_901_;
v_isShared_906_ = v_isSharedCheck_918_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_tail_903_);
lean_inc(v_head_902_);
lean_dec(v_x_901_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_918_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
lean_inc(v_x_899_);
if (v_isShared_906_ == 0)
{
lean_ctor_set_tag(v___x_905_, 5);
lean_ctor_set(v___x_905_, 1, v_x_899_);
lean_ctor_set(v___x_905_, 0, v_x_900_);
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_x_900_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_x_899_);
v___x_908_ = v_reuseFailAlloc_917_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = ((lean_object*)(l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__1));
v___x_911_ = l_String_quote(v_head_902_);
v___x_912_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
v___x_913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_910_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = l_Repr_addAppParen(v___x_913_, v___x_909_);
v___x_915_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_908_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2(v_x_899_, v___x_915_, v_tail_903_);
return v___x_916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0___lam__0(lean_object* v___y_919_){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = ((lean_object*)(l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__1));
v___x_922_ = l_String_quote(v___y_919_);
v___x_923_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
v___x_924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_921_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = l_Repr_addAppParen(v___x_924_, v___x_920_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0(lean_object* v_x_926_, lean_object* v_x_927_){
_start:
{
if (lean_obj_tag(v_x_926_) == 0)
{
lean_object* v___x_928_; 
lean_dec(v_x_927_);
v___x_928_ = lean_box(0);
return v___x_928_;
}
else
{
lean_object* v_tail_929_; 
v_tail_929_ = lean_ctor_get(v_x_926_, 1);
if (lean_obj_tag(v_tail_929_) == 0)
{
lean_object* v_head_930_; lean_object* v___x_931_; 
lean_dec(v_x_927_);
v_head_930_ = lean_ctor_get(v_x_926_, 0);
lean_inc(v_head_930_);
lean_dec_ref(v_x_926_);
v___x_931_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0___lam__0(v_head_930_);
return v___x_931_;
}
else
{
lean_object* v_head_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
lean_inc(v_tail_929_);
v_head_932_ = lean_ctor_get(v_x_926_, 0);
lean_inc(v_head_932_);
lean_dec_ref(v_x_926_);
v___x_933_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0___lam__0(v_head_932_);
v___x_934_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1(v_x_927_, v___x_933_, v_tail_929_);
return v___x_934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0(lean_object* v_xs_935_){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; uint8_t v___x_938_; 
v___x_936_ = lean_array_get_size(v_xs_935_);
v___x_937_ = lean_unsigned_to_nat(0u);
v___x_938_ = lean_nat_dec_eq(v___x_936_, v___x_937_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_939_ = lean_array_to_list(v_xs_935_);
v___x_940_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_941_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0(v___x_939_, v___x_940_);
v___x_942_ = lean_obj_once(&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4);
v___x_943_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5));
v___x_944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v___x_941_);
v___x_945_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6));
v___x_946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_942_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = l_Std_Format_fill(v___x_947_);
return v___x_948_;
}
else
{
lean_object* v___x_949_; 
lean_dec_ref(v_xs_935_);
v___x_949_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8));
return v___x_949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprImportArtifacts_repr___redArg(lean_object* v_x_959_){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; uint8_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_960_ = ((lean_object*)(l_Lean_instReprImportArtifacts_repr___redArg___closed__3));
v___x_961_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__4, &l_Lean_instReprModuleHeader_repr___redArg___closed__4_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__4);
v___x_962_ = l_Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0(v_x_959_);
v___x_963_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_961_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = 0;
v___x_965_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set_uint8(v___x_965_, sizeof(void*)*1, v___x_964_);
v___x_966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_960_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__20, &l_Lean_instReprImport_repr___redArg___closed__20_once, _init_l_Lean_instReprImport_repr___redArg___closed__20);
v___x_968_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__21));
v___x_969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v___x_966_);
v___x_970_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__22));
v___x_971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_967_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set_uint8(v___x_973_, sizeof(void*)*1, v___x_964_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprImportArtifacts_repr(lean_object* v_x_974_, lean_object* v_prec_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_instReprImportArtifacts_repr___redArg(v_x_974_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprImportArtifacts_repr___boxed(lean_object* v_x_977_, lean_object* v_prec_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_instReprImportArtifacts_repr(v_x_977_, v_prec_978_);
lean_dec(v_prec_978_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonImportArtifacts___lam__0(lean_object* v___f_986_, lean_object* v_x_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Array_toJson___redArg(v___f_986_, v_x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonImportArtifacts___lam__0(lean_object* v___f_993_, lean_object* v_x_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Array_fromJson_x3f___redArg(v___f_993_, v_x_994_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_995_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_995_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
v_a_1004_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_995_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_995_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_size(lean_object* v_arts_1016_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_array_get_size(v_arts_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_size___boxed(lean_object* v_arts_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_ImportArtifacts_size(v_arts_1018_);
lean_dec_ref(v_arts_1018_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_olean_x3f(lean_object* v_arts_1020_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; 
v___x_1021_ = lean_unsigned_to_nat(0u);
v___x_1022_ = lean_array_get_size(v_arts_1020_);
v___x_1023_ = lean_nat_dec_lt(v___x_1021_, v___x_1022_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; 
v___x_1024_ = lean_box(0);
return v___x_1024_;
}
else
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_array_fget_borrowed(v_arts_1020_, v___x_1021_);
lean_inc(v___x_1025_);
v___x_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
return v___x_1026_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_olean_x3f___boxed(lean_object* v_arts_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_ImportArtifacts_olean_x3f(v_arts_1027_);
lean_dec_ref(v_arts_1027_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_ir_x3f(lean_object* v_arts_1029_){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; uint8_t v___x_1032_; 
v___x_1030_ = lean_unsigned_to_nat(1u);
v___x_1031_ = lean_array_get_size(v_arts_1029_);
v___x_1032_ = lean_nat_dec_lt(v___x_1030_, v___x_1031_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_box(0);
return v___x_1033_;
}
else
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_array_fget_borrowed(v_arts_1029_, v___x_1030_);
lean_inc(v___x_1034_);
v___x_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
return v___x_1035_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_ir_x3f___boxed(lean_object* v_arts_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_ImportArtifacts_ir_x3f(v_arts_1036_);
lean_dec_ref(v_arts_1036_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanServer_x3f(lean_object* v_arts_1038_){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_1039_ = lean_unsigned_to_nat(2u);
v___x_1040_ = lean_array_get_size(v_arts_1038_);
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
v___x_1043_ = lean_array_fget_borrowed(v_arts_1038_, v___x_1039_);
lean_inc(v___x_1043_);
v___x_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
return v___x_1044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanServer_x3f___boxed(lean_object* v_arts_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_ImportArtifacts_oleanServer_x3f(v_arts_1045_);
lean_dec_ref(v_arts_1045_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanPrivate_x3f(lean_object* v_arts_1047_){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v___x_1048_ = lean_unsigned_to_nat(3u);
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
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_array_fget_borrowed(v_arts_1047_, v___x_1048_);
lean_inc(v___x_1052_);
v___x_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
return v___x_1053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanPrivate_x3f___boxed(lean_object* v_arts_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_ImportArtifacts_oleanPrivate_x3f(v_arts_1054_);
lean_dec_ref(v_arts_1054_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanParts(uint8_t v_inServer_1058_, lean_object* v_arts_1059_){
_start:
{
lean_object* v_fnames_1061_; lean_object* v_fnames_1065_; lean_object* v___x_1066_; 
v_fnames_1065_ = ((lean_object*)(l_Lean_ImportArtifacts_oleanParts___closed__0));
v___x_1066_ = l_Lean_ImportArtifacts_olean_x3f(v_arts_1059_);
if (lean_obj_tag(v___x_1066_) == 1)
{
lean_object* v_val_1067_; lean_object* v_fnames_1068_; lean_object* v___x_1069_; 
v_val_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_val_1067_);
lean_dec_ref(v___x_1066_);
v_fnames_1068_ = lean_array_push(v_fnames_1065_, v_val_1067_);
v___x_1069_ = l_Lean_ImportArtifacts_oleanServer_x3f(v_arts_1059_);
if (lean_obj_tag(v___x_1069_) == 1)
{
lean_object* v_val_1070_; 
v_val_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_val_1070_);
lean_dec_ref(v___x_1069_);
if (v_inServer_1058_ == 0)
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_ImportArtifacts_oleanPrivate_x3f(v_arts_1059_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_dec(v_val_1070_);
v_fnames_1061_ = v_fnames_1068_;
goto v___jp_1060_;
}
else
{
lean_dec_ref(v___x_1073_);
goto v___jp_1071_;
}
}
else
{
goto v___jp_1071_;
}
v___jp_1071_:
{
lean_object* v_fnames_1072_; 
v_fnames_1072_ = lean_array_push(v_fnames_1068_, v_val_1070_);
v_fnames_1061_ = v_fnames_1072_;
goto v___jp_1060_;
}
}
else
{
lean_dec(v___x_1069_);
return v_fnames_1068_;
}
}
else
{
lean_dec(v___x_1066_);
return v_fnames_1065_;
}
v___jp_1060_:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_ImportArtifacts_oleanPrivate_x3f(v_arts_1059_);
if (lean_obj_tag(v___x_1062_) == 1)
{
lean_object* v_val_1063_; lean_object* v_fnames_1064_; 
v_val_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_val_1063_);
lean_dec_ref(v___x_1062_);
v_fnames_1064_ = lean_array_push(v_fnames_1061_, v_val_1063_);
return v_fnames_1064_;
}
else
{
lean_dec(v___x_1062_);
return v_fnames_1061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportArtifacts_oleanParts___boxed(lean_object* v_inServer_1074_, lean_object* v_arts_1075_){
_start:
{
uint8_t v_inServer_boxed_1076_; lean_object* v_res_1077_; 
v_inServer_boxed_1076_ = lean_unbox(v_inServer_1074_);
v_res_1077_ = l_Lean_ImportArtifacts_oleanParts(v_inServer_boxed_1076_, v_arts_1075_);
lean_dec_ref(v_arts_1075_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(lean_object* v_x_1084_, lean_object* v_x_1085_){
_start:
{
if (lean_obj_tag(v_x_1084_) == 0)
{
lean_object* v___x_1086_; 
v___x_1086_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__1));
return v___x_1086_;
}
else
{
lean_object* v_val_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1102_; 
v_val_1087_ = lean_ctor_get(v_x_1084_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_x_1084_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1089_ = v_x_1084_;
v_isShared_1090_ = v_isSharedCheck_1102_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_val_1087_);
lean_dec(v_x_1084_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1102_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1091_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__3));
v___x_1092_ = lean_unsigned_to_nat(1024u);
v___x_1093_ = ((lean_object*)(l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__1));
v___x_1094_ = l_String_quote(v_val_1087_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set_tag(v___x_1089_, 3);
lean_ctor_set(v___x_1089_, 0, v___x_1094_);
v___x_1096_ = v___x_1089_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1097_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1093_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = l_Repr_addAppParen(v___x_1097_, v___x_1092_);
v___x_1099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1091_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = l_Repr_addAppParen(v___x_1099_, v_x_1085_);
return v___x_1100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___boxed(lean_object* v_x_1103_, lean_object* v_x_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_x_1103_, v_x_1104_);
lean_dec(v_x_1104_);
return v_res_1105_;
}
}
static lean_object* _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = lean_unsigned_to_nat(9u);
v___x_1116_ = lean_nat_to_int(v___x_1115_);
return v___x_1116_;
}
}
static lean_object* _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_unsigned_to_nat(16u);
v___x_1124_ = lean_nat_to_int(v___x_1123_);
return v___x_1124_;
}
}
static lean_object* _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_unsigned_to_nat(17u);
v___x_1129_ = lean_nat_to_int(v___x_1128_);
return v___x_1129_;
}
}
static lean_object* _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = lean_unsigned_to_nat(7u);
v___x_1137_ = lean_nat_to_int(v___x_1136_);
return v___x_1137_;
}
}
static lean_object* _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = lean_unsigned_to_nat(6u);
v___x_1142_ = lean_nat_to_int(v___x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleArtifacts_repr___redArg(lean_object* v_x_1146_){
_start:
{
lean_object* v_lean_x3f_1147_; lean_object* v_olean_x3f_1148_; lean_object* v_oleanServer_x3f_1149_; lean_object* v_oleanPrivate_x3f_1150_; lean_object* v_ilean_x3f_1151_; lean_object* v_ir_x3f_1152_; lean_object* v_c_x3f_1153_; lean_object* v_bc_x3f_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v_lean_x3f_1147_ = lean_ctor_get(v_x_1146_, 0);
lean_inc(v_lean_x3f_1147_);
v_olean_x3f_1148_ = lean_ctor_get(v_x_1146_, 1);
lean_inc(v_olean_x3f_1148_);
v_oleanServer_x3f_1149_ = lean_ctor_get(v_x_1146_, 2);
lean_inc(v_oleanServer_x3f_1149_);
v_oleanPrivate_x3f_1150_ = lean_ctor_get(v_x_1146_, 3);
lean_inc(v_oleanPrivate_x3f_1150_);
v_ilean_x3f_1151_ = lean_ctor_get(v_x_1146_, 4);
lean_inc(v_ilean_x3f_1151_);
v_ir_x3f_1152_ = lean_ctor_get(v_x_1146_, 5);
lean_inc(v_ir_x3f_1152_);
v_c_x3f_1153_ = lean_ctor_get(v_x_1146_, 6);
lean_inc(v_c_x3f_1153_);
v_bc_x3f_1154_ = lean_ctor_get(v_x_1146_, 7);
lean_inc(v_bc_x3f_1154_);
lean_dec_ref(v_x_1146_);
v___x_1155_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__5));
v___x_1156_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__3));
v___x_1157_ = lean_obj_once(&l_Lean_instReprModuleArtifacts_repr___redArg___closed__4, &l_Lean_instReprModuleArtifacts_repr___redArg___closed__4_once, _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__4);
v___x_1158_ = lean_unsigned_to_nat(0u);
v___x_1159_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_lean_x3f_1147_, v___x_1158_);
v___x_1160_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1157_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = 0;
v___x_1162_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1162_, 0, v___x_1160_);
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*1, v___x_1161_);
v___x_1163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1156_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__9));
v___x_1165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1163_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = lean_box(1);
v___x_1167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__6));
v___x_1169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1167_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
lean_ctor_set(v___x_1170_, 1, v___x_1155_);
v___x_1171_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__7, &l_Lean_instReprImport_repr___redArg___closed__7_once, _init_l_Lean_instReprImport_repr___redArg___closed__7);
v___x_1172_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_olean_x3f_1148_, v___x_1158_);
v___x_1173_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1171_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v___x_1174_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
lean_ctor_set_uint8(v___x_1174_, sizeof(void*)*1, v___x_1161_);
v___x_1175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1170_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
lean_ctor_set(v___x_1176_, 1, v___x_1164_);
v___x_1177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
lean_ctor_set(v___x_1177_, 1, v___x_1166_);
v___x_1178_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__8));
v___x_1179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1177_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
lean_ctor_set(v___x_1180_, 1, v___x_1155_);
v___x_1181_ = lean_obj_once(&l_Lean_instReprModuleArtifacts_repr___redArg___closed__9, &l_Lean_instReprModuleArtifacts_repr___redArg___closed__9_once, _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__9);
v___x_1182_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_oleanServer_x3f_1149_, v___x_1158_);
v___x_1183_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set_uint8(v___x_1184_, sizeof(void*)*1, v___x_1161_);
v___x_1185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1180_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
lean_ctor_set(v___x_1186_, 1, v___x_1164_);
v___x_1187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v___x_1166_);
v___x_1188_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__11));
v___x_1189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
lean_ctor_set(v___x_1190_, 1, v___x_1155_);
v___x_1191_ = lean_obj_once(&l_Lean_instReprModuleArtifacts_repr___redArg___closed__12, &l_Lean_instReprModuleArtifacts_repr___redArg___closed__12_once, _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__12);
v___x_1192_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_oleanPrivate_x3f_1150_, v___x_1158_);
v___x_1193_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1191_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
lean_ctor_set_uint8(v___x_1194_, sizeof(void*)*1, v___x_1161_);
v___x_1195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1190_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
lean_ctor_set(v___x_1196_, 1, v___x_1164_);
v___x_1197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set(v___x_1197_, 1, v___x_1166_);
v___x_1198_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__14));
v___x_1199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1197_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
lean_ctor_set(v___x_1200_, 1, v___x_1155_);
v___x_1201_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_ilean_x3f_1151_, v___x_1158_);
v___x_1202_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1171_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
lean_ctor_set_uint8(v___x_1203_, sizeof(void*)*1, v___x_1161_);
v___x_1204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1200_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
v___x_1205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
lean_ctor_set(v___x_1205_, 1, v___x_1164_);
v___x_1206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set(v___x_1206_, 1, v___x_1166_);
v___x_1207_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__16));
v___x_1208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1206_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v___x_1209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___x_1155_);
v___x_1210_ = lean_obj_once(&l_Lean_instReprModuleArtifacts_repr___redArg___closed__17, &l_Lean_instReprModuleArtifacts_repr___redArg___closed__17_once, _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__17);
v___x_1211_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_ir_x3f_1152_, v___x_1158_);
v___x_1212_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1210_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set_uint8(v___x_1213_, sizeof(void*)*1, v___x_1161_);
v___x_1214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1209_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
v___x_1215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
lean_ctor_set(v___x_1215_, 1, v___x_1164_);
v___x_1216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
lean_ctor_set(v___x_1216_, 1, v___x_1166_);
v___x_1217_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__19));
v___x_1218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1216_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
lean_ctor_set(v___x_1219_, 1, v___x_1155_);
v___x_1220_ = lean_obj_once(&l_Lean_instReprModuleArtifacts_repr___redArg___closed__20, &l_Lean_instReprModuleArtifacts_repr___redArg___closed__20_once, _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__20);
v___x_1221_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_c_x3f_1153_, v___x_1158_);
v___x_1222_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1220_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v___x_1223_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
lean_ctor_set_uint8(v___x_1223_, sizeof(void*)*1, v___x_1161_);
v___x_1224_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1219_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set(v___x_1225_, 1, v___x_1164_);
v___x_1226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v___x_1166_);
v___x_1227_ = ((lean_object*)(l_Lean_instReprModuleArtifacts_repr___redArg___closed__22));
v___x_1228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1226_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
lean_ctor_set(v___x_1229_, 1, v___x_1155_);
v___x_1230_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_bc_x3f_1154_, v___x_1158_);
v___x_1231_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1210_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
v___x_1232_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
lean_ctor_set_uint8(v___x_1232_, sizeof(void*)*1, v___x_1161_);
v___x_1233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1229_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__20, &l_Lean_instReprImport_repr___redArg___closed__20_once, _init_l_Lean_instReprImport_repr___redArg___closed__20);
v___x_1235_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__21));
v___x_1236_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
lean_ctor_set(v___x_1236_, 1, v___x_1233_);
v___x_1237_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__22));
v___x_1238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1236_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
v___x_1239_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1234_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
lean_ctor_set_uint8(v___x_1240_, sizeof(void*)*1, v___x_1161_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleArtifacts_repr(lean_object* v_x_1241_, lean_object* v_prec_1242_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_instReprModuleArtifacts_repr___redArg(v_x_1241_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleArtifacts_repr___boxed(lean_object* v_x_1244_, lean_object* v_prec_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_instReprModuleArtifacts_repr(v_x_1244_, v_prec_1245_);
lean_dec(v_prec_1245_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(lean_object* v_k_1253_, lean_object* v_x_1254_){
_start:
{
if (lean_obj_tag(v_x_1254_) == 0)
{
lean_object* v___x_1255_; 
lean_dec_ref(v_k_1253_);
v___x_1255_ = lean_box(0);
return v___x_1255_;
}
else
{
lean_object* v_val_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1266_; 
v_val_1256_ = lean_ctor_get(v_x_1254_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_x_1254_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1258_ = v_x_1254_;
v_isShared_1259_ = v_isSharedCheck_1266_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_val_1256_);
lean_dec(v_x_1254_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1266_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
lean_ctor_set_tag(v___x_1258_, 3);
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_val_1256_);
v___x_1261_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v_k_1253_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = lean_box(0);
v___x_1264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
return v___x_1264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonModuleArtifacts_toJson(lean_object* v_x_1275_){
_start:
{
lean_object* v_lean_x3f_1276_; lean_object* v_olean_x3f_1277_; lean_object* v_oleanServer_x3f_1278_; lean_object* v_oleanPrivate_x3f_1279_; lean_object* v_ilean_x3f_1280_; lean_object* v_ir_x3f_1281_; lean_object* v_c_x3f_1282_; lean_object* v_bc_x3f_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v_lean_x3f_1276_ = lean_ctor_get(v_x_1275_, 0);
lean_inc(v_lean_x3f_1276_);
v_olean_x3f_1277_ = lean_ctor_get(v_x_1275_, 1);
lean_inc(v_olean_x3f_1277_);
v_oleanServer_x3f_1278_ = lean_ctor_get(v_x_1275_, 2);
lean_inc(v_oleanServer_x3f_1278_);
v_oleanPrivate_x3f_1279_ = lean_ctor_get(v_x_1275_, 3);
lean_inc(v_oleanPrivate_x3f_1279_);
v_ilean_x3f_1280_ = lean_ctor_get(v_x_1275_, 4);
lean_inc(v_ilean_x3f_1280_);
v_ir_x3f_1281_ = lean_ctor_get(v_x_1275_, 5);
lean_inc(v_ir_x3f_1281_);
v_c_x3f_1282_ = lean_ctor_get(v_x_1275_, 6);
lean_inc(v_c_x3f_1282_);
v_bc_x3f_1283_ = lean_ctor_get(v_x_1275_, 7);
lean_inc(v_bc_x3f_1283_);
lean_dec_ref(v_x_1275_);
v___x_1284_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__0));
v___x_1285_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1284_, v_lean_x3f_1276_);
v___x_1286_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__1));
v___x_1287_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1286_, v_olean_x3f_1277_);
v___x_1288_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__2));
v___x_1289_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1288_, v_oleanServer_x3f_1278_);
v___x_1290_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__3));
v___x_1291_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1290_, v_oleanPrivate_x3f_1279_);
v___x_1292_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__4));
v___x_1293_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1292_, v_ilean_x3f_1280_);
v___x_1294_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__5));
v___x_1295_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1294_, v_ir_x3f_1281_);
v___x_1296_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__6));
v___x_1297_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1296_, v_c_x3f_1282_);
v___x_1298_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__7));
v___x_1299_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(v___x_1298_, v_bc_x3f_1283_);
v___x_1300_ = lean_box(0);
v___x_1301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v___x_1302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1297_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
v___x_1303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1295_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
v___x_1304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1293_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
v___x_1305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1291_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
v___x_1306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1289_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1287_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
v___x_1308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1285_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v___x_1309_ = ((lean_object*)(l_Lean_instToJsonImport_toJson___closed__0));
v___x_1310_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(v___x_1308_, v___x_1309_);
v___x_1311_ = l_Lean_Json_mkObj(v___x_1310_);
lean_dec(v___x_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0(lean_object* v_x_1316_){
_start:
{
if (lean_obj_tag(v_x_1316_) == 0)
{
lean_object* v___x_1317_; 
v___x_1317_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0___closed__0));
return v___x_1317_;
}
else
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Lean_Json_getStr_x3f(v_x_1316_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1318_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1318_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1335_; 
v_a_1327_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1329_ = v___x_1318_;
v_isShared_1330_ = v_isSharedCheck_1335_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1318_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1335_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1331_, 0, v_a_1327_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1331_);
v___x_1333_ = v___x_1329_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(lean_object* v_j_1336_, lean_object* v_k_1337_){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = l_Lean_Json_getObjValD(v_j_1336_, v_k_1337_);
v___x_1339_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0(v___x_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0___boxed(lean_object* v_j_1340_, lean_object* v_k_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_j_1340_, v_k_1341_);
lean_dec_ref(v_k_1341_);
return v_res_1342_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1347_ = 1;
v___x_1348_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__1));
v___x_1349_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1348_, v___x_1347_);
return v___x_1349_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__4));
v___x_1351_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2);
v___x_1352_ = lean_string_append(v___x_1351_, v___x_1350_);
return v___x_1352_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1355_ = 1;
v___x_1356_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__4));
v___x_1357_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1356_, v___x_1355_);
return v___x_1357_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1358_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5);
v___x_1359_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1360_ = lean_string_append(v___x_1359_, v___x_1358_);
return v___x_1360_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1361_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1362_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6);
v___x_1363_ = lean_string_append(v___x_1362_, v___x_1361_);
return v___x_1363_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1366_ = 1;
v___x_1367_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__8));
v___x_1368_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1367_, v___x_1366_);
return v___x_1368_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1369_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9);
v___x_1370_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1371_ = lean_string_append(v___x_1370_, v___x_1369_);
return v___x_1371_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1372_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1373_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10);
v___x_1374_ = lean_string_append(v___x_1373_, v___x_1372_);
return v___x_1374_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13(void){
_start:
{
uint8_t v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1377_ = 1;
v___x_1378_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__12));
v___x_1379_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1378_, v___x_1377_);
return v___x_1379_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13);
v___x_1381_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1382_ = lean_string_append(v___x_1381_, v___x_1380_);
return v___x_1382_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1383_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1384_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14);
v___x_1385_ = lean_string_append(v___x_1384_, v___x_1383_);
return v___x_1385_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17(void){
_start:
{
uint8_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1388_ = 1;
v___x_1389_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__16));
v___x_1390_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1389_, v___x_1388_);
return v___x_1390_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18(void){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1391_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17);
v___x_1392_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1393_ = lean_string_append(v___x_1392_, v___x_1391_);
return v___x_1393_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1394_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1395_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18);
v___x_1396_ = lean_string_append(v___x_1395_, v___x_1394_);
return v___x_1396_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1399_ = 1;
v___x_1400_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__20));
v___x_1401_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1400_, v___x_1399_);
return v___x_1401_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1402_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21);
v___x_1403_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1404_ = lean_string_append(v___x_1403_, v___x_1402_);
return v___x_1404_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1405_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1406_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22);
v___x_1407_ = lean_string_append(v___x_1406_, v___x_1405_);
return v___x_1407_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25(void){
_start:
{
uint8_t v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1410_ = 1;
v___x_1411_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__24));
v___x_1412_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1411_, v___x_1410_);
return v___x_1412_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1413_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25);
v___x_1414_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1415_ = lean_string_append(v___x_1414_, v___x_1413_);
return v___x_1415_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1416_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1417_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26);
v___x_1418_ = lean_string_append(v___x_1417_, v___x_1416_);
return v___x_1418_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29(void){
_start:
{
uint8_t v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1421_ = 1;
v___x_1422_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__28));
v___x_1423_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1422_, v___x_1421_);
return v___x_1423_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30(void){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1424_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29);
v___x_1425_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1426_ = lean_string_append(v___x_1425_, v___x_1424_);
return v___x_1426_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31(void){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1427_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1428_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30);
v___x_1429_ = lean_string_append(v___x_1428_, v___x_1427_);
return v___x_1429_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33(void){
_start:
{
uint8_t v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1432_ = 1;
v___x_1433_ = ((lean_object*)(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__32));
v___x_1434_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1433_, v___x_1432_);
return v___x_1434_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34(void){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1435_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33);
v___x_1436_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3);
v___x_1437_ = lean_string_append(v___x_1436_, v___x_1435_);
return v___x_1437_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35(void){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1438_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_1439_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34);
v___x_1440_ = lean_string_append(v___x_1439_, v___x_1438_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson(lean_object* v_json_1441_){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1442_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__0));
lean_inc(v_json_1441_);
v___x_1443_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1441_, v___x_1442_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1453_; 
lean_dec(v_json_1441_);
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1446_ = v___x_1443_;
v_isShared_1447_ = v_isSharedCheck_1453_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1443_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1453_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1448_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7);
v___x_1449_ = lean_string_append(v___x_1448_, v_a_1444_);
lean_dec(v_a_1444_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 0, v___x_1449_);
v___x_1451_ = v___x_1446_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
else
{
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec(v_json_1441_);
v_a_1454_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1443_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1443_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
lean_ctor_set_tag(v___x_1456_, 0);
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v_a_1462_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_a_1462_);
lean_dec_ref(v___x_1443_);
v___x_1463_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__1));
lean_inc(v_json_1441_);
v___x_1464_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1441_, v___x_1463_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1474_; 
lean_dec(v_a_1462_);
lean_dec(v_json_1441_);
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1467_ = v___x_1464_;
v_isShared_1468_ = v_isSharedCheck_1474_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1464_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1474_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1472_; 
v___x_1469_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11);
v___x_1470_ = lean_string_append(v___x_1469_, v_a_1465_);
lean_dec(v_a_1465_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v___x_1470_);
v___x_1472_ = v___x_1467_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
else
{
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_dec(v_a_1462_);
lean_dec(v_json_1441_);
v_a_1475_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1464_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1464_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
lean_ctor_set_tag(v___x_1477_, 0);
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v_a_1483_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_a_1483_);
lean_dec_ref(v___x_1464_);
v___x_1484_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__2));
lean_inc(v_json_1441_);
v___x_1485_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1441_, v___x_1484_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1495_; 
lean_dec(v_a_1483_);
lean_dec(v_a_1462_);
lean_dec(v_json_1441_);
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1495_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1495_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1490_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15);
v___x_1491_ = lean_string_append(v___x_1490_, v_a_1486_);
lean_dec(v_a_1486_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1491_);
v___x_1493_ = v___x_1488_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
else
{
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_dec(v_a_1483_);
lean_dec(v_a_1462_);
lean_dec(v_json_1441_);
v_a_1496_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1485_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1485_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
lean_ctor_set_tag(v___x_1498_, 0);
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v_a_1504_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_a_1504_);
lean_dec_ref(v___x_1485_);
v___x_1505_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__3));
lean_inc(v_json_1441_);
v___x_1506_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1441_, v___x_1505_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1516_; 
lean_dec(v_a_1504_);
lean_dec(v_a_1483_);
lean_dec(v_a_1462_);
lean_dec(v_json_1441_);
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1509_ = v___x_1506_;
v_isShared_1510_ = v_isSharedCheck_1516_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1506_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1516_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1511_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19);
v___x_1512_ = lean_string_append(v___x_1511_, v_a_1507_);
lean_dec(v_a_1507_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v___x_1512_);
v___x_1514_ = v___x_1509_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
else
{
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
lean_dec(v_a_1504_);
lean_dec(v_a_1483_);
lean_dec(v_a_1462_);
lean_dec(v_json_1441_);
v_a_1517_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1519_ = v___x_1506_;
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1506_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
if (v_isShared_1520_ == 0)
{
lean_ctor_set_tag(v___x_1519_, 0);
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1517_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v_a_1525_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_a_1525_);
lean_dec_ref(v___x_1506_);
v___x_1526_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__4));
lean_inc(v_json_1441_);
v___x_1527_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1441_, v___x_1526_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1537_; 
lean_dec(v_a_1525_);
lean_dec(v_a_1504_);
lean_dec(v_a_1483_);
lean_dec(v_a_1462_);
lean_dec(v_json_1441_);
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1530_ = v___x_1527_;
v_isShared_1531_ = v_isSharedCheck_1537_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1527_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1537_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1532_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23);
v___x_1533_ = lean_string_append(v___x_1532_, v_a_1528_);
lean_dec(v_a_1528_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v___x_1533_);
v___x_1535_ = v___x_1530_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
else
{
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_dec(v_a_1525_);
lean_dec(v_a_1504_);
lean_dec(v_a_1483_);
lean_dec(v_a_1462_);
lean_dec(v_json_1441_);
v_a_1538_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1527_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1527_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
lean_ctor_set_tag(v___x_1540_, 0);
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_a_1546_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1546_);
lean_dec_ref(v___x_1527_);
v___x_1547_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__5));
lean_inc(v_json_1441_);
v___x_1548_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1441_, v___x_1547_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1558_; 
lean_dec(v_a_1546_);
lean_dec(v_a_1525_);
lean_dec(v_a_1504_);
lean_dec(v_a_1483_);
lean_dec(v_a_1462_);
lean_dec(v_json_1441_);
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1551_ = v___x_1548_;
v_isShared_1552_ = v_isSharedCheck_1558_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1548_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1558_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1556_; 
v___x_1553_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27);
v___x_1554_ = lean_string_append(v___x_1553_, v_a_1549_);
lean_dec(v_a_1549_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1554_);
v___x_1556_ = v___x_1551_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
else
{
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec(v_a_1546_);
lean_dec(v_a_1525_);
lean_dec(v_a_1504_);
lean_dec(v_a_1483_);
lean_dec(v_a_1462_);
lean_dec(v_json_1441_);
v_a_1559_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1548_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1548_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
lean_ctor_set_tag(v___x_1561_, 0);
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_a_1567_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1567_);
lean_dec_ref(v___x_1548_);
v___x_1568_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__6));
lean_inc(v_json_1441_);
v___x_1569_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1441_, v___x_1568_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1579_; 
lean_dec(v_a_1567_);
lean_dec(v_a_1546_);
lean_dec(v_a_1525_);
lean_dec(v_a_1504_);
lean_dec(v_a_1483_);
lean_dec(v_a_1462_);
lean_dec(v_json_1441_);
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1572_ = v___x_1569_;
v_isShared_1573_ = v_isSharedCheck_1579_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1569_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1579_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1574_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31);
v___x_1575_ = lean_string_append(v___x_1574_, v_a_1570_);
lean_dec(v_a_1570_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v___x_1575_);
v___x_1577_ = v___x_1572_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
else
{
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec(v_a_1567_);
lean_dec(v_a_1546_);
lean_dec(v_a_1525_);
lean_dec(v_a_1504_);
lean_dec(v_a_1483_);
lean_dec(v_a_1462_);
lean_dec(v_json_1441_);
v_a_1580_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1569_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1569_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
lean_ctor_set_tag(v___x_1582_, 0);
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v_a_1588_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1588_);
lean_dec_ref(v___x_1569_);
v___x_1589_ = ((lean_object*)(l_Lean_instToJsonModuleArtifacts_toJson___closed__7));
v___x_1590_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_1441_, v___x_1589_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1600_; 
lean_dec(v_a_1588_);
lean_dec(v_a_1567_);
lean_dec(v_a_1546_);
lean_dec(v_a_1525_);
lean_dec(v_a_1504_);
lean_dec(v_a_1483_);
lean_dec(v_a_1462_);
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1600_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1600_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1595_ = lean_obj_once(&l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35, &l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35_once, _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35);
v___x_1596_ = lean_string_append(v___x_1595_, v_a_1591_);
lean_dec(v_a_1591_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v___x_1596_);
v___x_1598_ = v___x_1593_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
else
{
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec(v_a_1588_);
lean_dec(v_a_1567_);
lean_dec(v_a_1546_);
lean_dec(v_a_1525_);
lean_dec(v_a_1504_);
lean_dec(v_a_1483_);
lean_dec(v_a_1462_);
v_a_1601_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1590_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1590_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
lean_ctor_set_tag(v___x_1603_, 0);
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1617_; 
v_a_1609_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1611_ = v___x_1590_;
v_isShared_1612_ = v_isSharedCheck_1617_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1590_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1617_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1613_; lean_object* v___x_1615_; 
v___x_1613_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1613_, 0, v_a_1462_);
lean_ctor_set(v___x_1613_, 1, v_a_1483_);
lean_ctor_set(v___x_1613_, 2, v_a_1504_);
lean_ctor_set(v___x_1613_, 3, v_a_1525_);
lean_ctor_set(v___x_1613_, 4, v_a_1546_);
lean_ctor_set(v___x_1613_, 5, v_a_1567_);
lean_ctor_set(v___x_1613_, 6, v_a_1588_);
lean_ctor_set(v___x_1613_, 7, v_a_1609_);
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 0, v___x_1613_);
v___x_1615_ = v___x_1611_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
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
LEAN_EXPORT lean_object* l_Lean_ModuleArtifacts_oleanParts(lean_object* v_arts_1620_){
_start:
{
lean_object* v_olean_x3f_1621_; lean_object* v_oleanServer_x3f_1622_; lean_object* v_oleanPrivate_x3f_1623_; lean_object* v_fnames_1624_; 
v_olean_x3f_1621_ = lean_ctor_get(v_arts_1620_, 1);
lean_inc(v_olean_x3f_1621_);
v_oleanServer_x3f_1622_ = lean_ctor_get(v_arts_1620_, 2);
lean_inc(v_oleanServer_x3f_1622_);
v_oleanPrivate_x3f_1623_ = lean_ctor_get(v_arts_1620_, 3);
lean_inc(v_oleanPrivate_x3f_1623_);
lean_dec_ref(v_arts_1620_);
v_fnames_1624_ = ((lean_object*)(l_Lean_ImportArtifacts_oleanParts___closed__0));
if (lean_obj_tag(v_olean_x3f_1621_) == 1)
{
lean_object* v_val_1625_; lean_object* v_fnames_1626_; 
v_val_1625_ = lean_ctor_get(v_olean_x3f_1621_, 0);
lean_inc(v_val_1625_);
lean_dec_ref(v_olean_x3f_1621_);
v_fnames_1626_ = lean_array_push(v_fnames_1624_, v_val_1625_);
if (lean_obj_tag(v_oleanServer_x3f_1622_) == 1)
{
lean_object* v_val_1627_; lean_object* v_fnames_1628_; 
v_val_1627_ = lean_ctor_get(v_oleanServer_x3f_1622_, 0);
lean_inc(v_val_1627_);
lean_dec_ref(v_oleanServer_x3f_1622_);
v_fnames_1628_ = lean_array_push(v_fnames_1626_, v_val_1627_);
if (lean_obj_tag(v_oleanPrivate_x3f_1623_) == 1)
{
lean_object* v_val_1629_; lean_object* v_fnames_1630_; 
v_val_1629_ = lean_ctor_get(v_oleanPrivate_x3f_1623_, 0);
lean_inc(v_val_1629_);
lean_dec_ref(v_oleanPrivate_x3f_1623_);
v_fnames_1630_ = lean_array_push(v_fnames_1628_, v_val_1629_);
return v_fnames_1630_;
}
else
{
lean_dec(v_oleanPrivate_x3f_1623_);
return v_fnames_1628_;
}
}
else
{
lean_dec(v_oleanPrivate_x3f_1623_);
lean_dec(v_oleanServer_x3f_1622_);
return v_fnames_1626_;
}
}
else
{
lean_dec(v_oleanPrivate_x3f_1623_);
lean_dec(v_oleanServer_x3f_1622_);
lean_dec(v_olean_x3f_1621_);
return v_fnames_1624_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0(lean_object* v_x_1631_, lean_object* v_x_1632_){
_start:
{
if (lean_obj_tag(v_x_1631_) == 0)
{
lean_object* v___x_1633_; 
v___x_1633_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__1));
return v___x_1633_;
}
else
{
lean_object* v_val_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1645_; 
v_val_1634_ = lean_ctor_get(v_x_1631_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_x_1631_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1636_ = v_x_1631_;
v_isShared_1637_ = v_isSharedCheck_1645_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_val_1634_);
lean_dec(v_x_1631_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1645_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1638_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__3));
v___x_1639_ = l_String_quote(v_val_1634_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set_tag(v___x_1636_, 3);
lean_ctor_set(v___x_1636_, 0, v___x_1639_);
v___x_1641_ = v___x_1636_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1638_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = l_Repr_addAppParen(v___x_1642_, v_x_1632_);
return v___x_1643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0___boxed(lean_object* v_x_1646_, lean_object* v_x_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0(v_x_1646_, v_x_1647_);
lean_dec(v_x_1647_);
return v_res_1648_;
}
}
static lean_object* _init_l_Lean_instReprPlugin_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = lean_unsigned_to_nat(8u);
v___x_1659_ = lean_nat_to_int(v___x_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprPlugin_repr___redArg(lean_object* v_x_1663_){
_start:
{
lean_object* v_path_1664_; lean_object* v_initFn_x3f_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1703_; 
v_path_1664_ = lean_ctor_get(v_x_1663_, 0);
v_initFn_x3f_1665_ = lean_ctor_get(v_x_1663_, 1);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_x_1663_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1667_ = v_x_1663_;
v_isShared_1668_ = v_isSharedCheck_1703_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_initFn_x3f_1665_);
lean_inc(v_path_1664_);
lean_dec(v_x_1663_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1703_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1669_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__5));
v___x_1670_ = ((lean_object*)(l_Lean_instReprPlugin_repr___redArg___closed__3));
v___x_1671_ = lean_obj_once(&l_Lean_instReprPlugin_repr___redArg___closed__4, &l_Lean_instReprPlugin_repr___redArg___closed__4_once, _init_l_Lean_instReprPlugin_repr___redArg___closed__4);
v___x_1672_ = lean_unsigned_to_nat(0u);
v___x_1673_ = ((lean_object*)(l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__1));
v___x_1674_ = l_String_quote(v_path_1664_);
v___x_1675_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set_tag(v___x_1667_, 5);
lean_ctor_set(v___x_1667_, 1, v___x_1675_);
lean_ctor_set(v___x_1667_, 0, v___x_1673_);
v___x_1677_ = v___x_1667_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1678_ = l_Repr_addAppParen(v___x_1677_, v___x_1672_);
v___x_1679_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1671_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = 0;
v___x_1681_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set_uint8(v___x_1681_, sizeof(void*)*1, v___x_1680_);
v___x_1682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1670_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
v___x_1683_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__9));
v___x_1684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1682_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
v___x_1685_ = lean_box(1);
v___x_1686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1684_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
v___x_1687_ = ((lean_object*)(l_Lean_instReprPlugin_repr___redArg___closed__6));
v___x_1688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1686_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
v___x_1689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
lean_ctor_set(v___x_1689_, 1, v___x_1669_);
v___x_1690_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__4, &l_Lean_instReprModuleHeader_repr___redArg___closed__4_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__4);
v___x_1691_ = l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0(v_initFn_x3f_1665_, v___x_1672_);
v___x_1692_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1690_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
v___x_1693_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
lean_ctor_set_uint8(v___x_1693_, sizeof(void*)*1, v___x_1680_);
v___x_1694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1689_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
v___x_1695_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__20, &l_Lean_instReprImport_repr___redArg___closed__20_once, _init_l_Lean_instReprImport_repr___redArg___closed__20);
v___x_1696_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__21));
v___x_1697_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
lean_ctor_set(v___x_1697_, 1, v___x_1694_);
v___x_1698_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__22));
v___x_1699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1697_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1695_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1701_, 0, v___x_1700_);
lean_ctor_set_uint8(v___x_1701_, sizeof(void*)*1, v___x_1680_);
return v___x_1701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprPlugin_repr(lean_object* v_x_1704_, lean_object* v_prec_1705_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Lean_instReprPlugin_repr___redArg(v_x_1704_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprPlugin_repr___boxed(lean_object* v_x_1707_, lean_object* v_prec_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_instReprPlugin_repr(v_x_1707_, v_prec_1708_);
lean_dec(v_prec_1708_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonPlugin_toJson_spec__0(lean_object* v_k_1712_, lean_object* v_x_1713_){
_start:
{
if (lean_obj_tag(v_x_1713_) == 0)
{
lean_object* v___x_1714_; 
lean_dec_ref(v_k_1712_);
v___x_1714_ = lean_box(0);
return v___x_1714_;
}
else
{
lean_object* v_val_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1725_; 
v_val_1715_ = lean_ctor_get(v_x_1713_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_x_1713_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1717_ = v_x_1713_;
v_isShared_1718_ = v_isSharedCheck_1725_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_val_1715_);
lean_dec(v_x_1713_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1725_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
lean_ctor_set_tag(v___x_1717_, 3);
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_val_1715_);
v___x_1720_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1721_, 0, v_k_1712_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
v___x_1722_ = lean_box(0);
v___x_1723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1721_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
return v___x_1723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonPlugin_toJson(lean_object* v_x_1727_){
_start:
{
lean_object* v_path_1728_; lean_object* v_initFn_x3f_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1747_; 
v_path_1728_ = lean_ctor_get(v_x_1727_, 0);
v_initFn_x3f_1729_ = lean_ctor_get(v_x_1727_, 1);
v_isSharedCheck_1747_ = !lean_is_exclusive(v_x_1727_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1731_ = v_x_1727_;
v_isShared_1732_ = v_isSharedCheck_1747_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_initFn_x3f_1729_);
lean_inc(v_path_1728_);
lean_dec(v_x_1727_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1747_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; 
v___x_1733_ = ((lean_object*)(l_Lean_instReprPlugin_repr___redArg___closed__0));
v___x_1734_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1734_, 0, v_path_1728_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 1, v___x_1734_);
lean_ctor_set(v___x_1731_, 0, v___x_1733_);
v___x_1736_ = v___x_1731_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1733_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v___x_1734_);
v___x_1736_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1737_ = lean_box(0);
v___x_1738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1736_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = ((lean_object*)(l_Lean_instToJsonPlugin_toJson___closed__0));
v___x_1740_ = l_Lean_Json_opt___at___00Lean_instToJsonPlugin_toJson_spec__0(v___x_1739_, v_initFn_x3f_1729_);
v___x_1741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
lean_ctor_set(v___x_1741_, 1, v___x_1737_);
v___x_1742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1738_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
v___x_1743_ = ((lean_object*)(l_Lean_instToJsonImport_toJson___closed__0));
v___x_1744_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(v___x_1742_, v___x_1743_);
v___x_1745_ = l_Lean_Json_mkObj(v___x_1744_);
lean_dec(v___x_1744_);
return v___x_1745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Plugin_ofFilePath(lean_object* v_path_1750_){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = lean_box(0);
v___x_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1752_, 0, v_path_1750_);
lean_ctor_set(v___x_1752_, 1, v___x_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__0(lean_object* v_j_1755_, lean_object* v_k_1756_){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = l_Lean_Json_getObjValD(v_j_1755_, v_k_1756_);
v___x_1758_ = l_Lean_Json_getStr_x3f(v___x_1757_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
v_a_1767_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1758_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1758_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__0___boxed(lean_object* v_j_1775_, lean_object* v_k_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__0(v_j_1775_, v_k_1776_);
lean_dec_ref(v_k_1776_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1_spec__1(lean_object* v_x_1778_){
_start:
{
if (lean_obj_tag(v_x_1778_) == 0)
{
lean_object* v___x_1779_; 
v___x_1779_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0___closed__0));
return v___x_1779_;
}
else
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Lean_Json_getStr_x3f(v_x_1778_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1780_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1780_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1797_; 
v_a_1789_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1791_ = v___x_1780_;
v_isShared_1792_ = v_isSharedCheck_1797_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1780_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1797_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1793_; lean_object* v___x_1795_; 
v___x_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1793_, 0, v_a_1789_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 0, v___x_1793_);
v___x_1795_ = v___x_1791_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1(lean_object* v_j_1798_, lean_object* v_k_1799_){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = l_Lean_Json_getObjValD(v_j_1798_, v_k_1799_);
v___x_1801_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1_spec__1(v___x_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1___boxed(lean_object* v_j_1802_, lean_object* v_k_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1(v_j_1802_, v_k_1803_);
lean_dec_ref(v_k_1803_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Plugin_fromJson_x3f(lean_object* v_data_1808_){
_start:
{
switch(lean_obj_tag(v_data_1808_))
{
case 3:
{
lean_object* v_s_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1817_; 
v_s_1809_ = lean_ctor_get(v_data_1808_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v_data_1808_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1811_ = v_data_1808_;
v_isShared_1812_ = v_isSharedCheck_1817_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_s_1809_);
lean_dec(v_data_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1817_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1813_ = l_Lean_Plugin_ofFilePath(v_s_1809_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set_tag(v___x_1811_, 1);
lean_ctor_set(v___x_1811_, 0, v___x_1813_);
v___x_1815_ = v___x_1811_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
case 5:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = ((lean_object*)(l_Lean_instReprPlugin_repr___redArg___closed__0));
lean_inc_ref(v_data_1808_);
v___x_1819_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__0(v_data_1808_, v___x_1818_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_dec_ref(v_data_1808_);
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1819_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
else
{
lean_object* v_a_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v_a_1828_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1828_);
lean_dec_ref(v___x_1819_);
v___x_1829_ = ((lean_object*)(l_Lean_instToJsonPlugin_toJson___closed__0));
v___x_1830_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1(v_data_1808_, v___x_1829_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
lean_dec(v_a_1828_);
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
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1847_; 
v_a_1839_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1841_ = v___x_1830_;
v_isShared_1842_ = v_isSharedCheck_1847_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1830_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1847_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1843_; lean_object* v___x_1845_; 
v___x_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1843_, 0, v_a_1828_);
lean_ctor_set(v___x_1843_, 1, v_a_1839_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v___x_1843_);
v___x_1845_ = v___x_1841_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
}
default: 
{
lean_object* v___x_1848_; 
lean_dec(v_data_1808_);
v___x_1848_ = ((lean_object*)(l_Lean_Plugin_fromJson_x3f___closed__1));
return v___x_1848_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2_spec__3_spec__5(lean_object* v_x_1851_, lean_object* v_x_1852_, lean_object* v_x_1853_){
_start:
{
if (lean_obj_tag(v_x_1853_) == 0)
{
lean_dec(v_x_1851_);
return v_x_1852_;
}
else
{
lean_object* v_head_1854_; lean_object* v_tail_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1864_; 
v_head_1854_ = lean_ctor_get(v_x_1853_, 0);
v_tail_1855_ = lean_ctor_get(v_x_1853_, 1);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_x_1853_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1857_ = v_x_1853_;
v_isShared_1858_ = v_isSharedCheck_1864_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_tail_1855_);
lean_inc(v_head_1854_);
lean_dec(v_x_1853_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1864_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
lean_inc(v_x_1851_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set_tag(v___x_1857_, 5);
lean_ctor_set(v___x_1857_, 1, v_x_1851_);
lean_ctor_set(v___x_1857_, 0, v_x_1852_);
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_x_1852_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_x_1851_);
v___x_1860_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
lean_object* v___x_1861_; 
v___x_1861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
lean_ctor_set(v___x_1861_, 1, v_head_1854_);
v_x_1852_ = v___x_1861_;
v_x_1853_ = v_tail_1855_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2_spec__3(lean_object* v_x_1865_, lean_object* v_x_1866_){
_start:
{
if (lean_obj_tag(v_x_1865_) == 0)
{
lean_object* v___x_1867_; 
lean_dec(v_x_1866_);
v___x_1867_ = lean_box(0);
return v___x_1867_;
}
else
{
lean_object* v_tail_1868_; 
v_tail_1868_ = lean_ctor_get(v_x_1865_, 1);
if (lean_obj_tag(v_tail_1868_) == 0)
{
lean_object* v_head_1869_; 
lean_dec(v_x_1866_);
v_head_1869_ = lean_ctor_get(v_x_1865_, 0);
lean_inc(v_head_1869_);
lean_dec_ref(v_x_1865_);
return v_head_1869_;
}
else
{
lean_object* v_head_1870_; lean_object* v___x_1871_; 
lean_inc(v_tail_1868_);
v_head_1870_ = lean_ctor_get(v_x_1865_, 0);
lean_inc(v_head_1870_);
lean_dec_ref(v_x_1865_);
v___x_1871_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2_spec__3_spec__5(v_x_1866_, v_head_1870_, v_tail_1868_);
return v___x_1871_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__0));
v___x_1875_ = lean_string_length(v___x_1874_);
return v___x_1875_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2, &l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2);
v___x_1877_ = lean_nat_to_int(v___x_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(lean_object* v_x_1882_){
_start:
{
lean_object* v_fst_1883_; lean_object* v_snd_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1907_; 
v_fst_1883_ = lean_ctor_get(v_x_1882_, 0);
v_snd_1884_ = lean_ctor_get(v_x_1882_, 1);
v_isSharedCheck_1907_ = !lean_is_exclusive(v_x_1882_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1886_ = v_x_1882_;
v_isShared_1887_ = v_isSharedCheck_1907_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_snd_1884_);
lean_inc(v_fst_1883_);
lean_dec(v_x_1882_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1907_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1888_ = lean_unsigned_to_nat(0u);
v___x_1889_ = l_Lean_Name_reprPrec(v_fst_1883_, v___x_1888_);
v___x_1890_ = lean_box(0);
if (v_isShared_1887_ == 0)
{
lean_ctor_set_tag(v___x_1886_, 1);
lean_ctor_set(v___x_1886_, 1, v___x_1890_);
lean_ctor_set(v___x_1886_, 0, v___x_1889_);
v___x_1892_ = v___x_1886_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; uint8_t v___x_1904_; lean_object* v___x_1905_; 
v___x_1893_ = l_Lean_instReprImportArtifacts_repr___redArg(v_snd_1884_);
v___x_1894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
lean_ctor_set(v___x_1894_, 1, v___x_1892_);
v___x_1895_ = l_List_reverse___redArg(v___x_1894_);
v___x_1896_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_1897_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2_spec__3(v___x_1895_, v___x_1896_);
v___x_1898_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3);
v___x_1899_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__4));
v___x_1900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
lean_ctor_set(v___x_1900_, 1, v___x_1897_);
v___x_1901_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__5));
v___x_1902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1900_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
v___x_1903_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1898_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = 0;
v___x_1905_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set_uint8(v___x_1905_, sizeof(void*)*1, v___x_1904_);
return v___x_1905_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3_spec__5_spec__8(lean_object* v_x_1908_, lean_object* v_x_1909_, lean_object* v_x_1910_){
_start:
{
if (lean_obj_tag(v_x_1910_) == 0)
{
lean_dec(v_x_1908_);
return v_x_1909_;
}
else
{
lean_object* v_head_1911_; lean_object* v_tail_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1922_; 
v_head_1911_ = lean_ctor_get(v_x_1910_, 0);
v_tail_1912_ = lean_ctor_get(v_x_1910_, 1);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_x_1910_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1914_ = v_x_1910_;
v_isShared_1915_ = v_isSharedCheck_1922_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_tail_1912_);
lean_inc(v_head_1911_);
lean_dec(v_x_1910_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1922_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
lean_inc(v_x_1908_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set_tag(v___x_1914_, 5);
lean_ctor_set(v___x_1914_, 1, v_x_1908_);
lean_ctor_set(v___x_1914_, 0, v_x_1909_);
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_x_1909_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_x_1908_);
v___x_1917_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_head_1911_);
v___x_1919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v_x_1909_ = v___x_1919_;
v_x_1910_ = v_tail_1912_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3_spec__5(lean_object* v_x_1923_, lean_object* v_x_1924_, lean_object* v_x_1925_){
_start:
{
if (lean_obj_tag(v_x_1925_) == 0)
{
lean_dec(v_x_1923_);
return v_x_1924_;
}
else
{
lean_object* v_head_1926_; lean_object* v_tail_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1937_; 
v_head_1926_ = lean_ctor_get(v_x_1925_, 0);
v_tail_1927_ = lean_ctor_get(v_x_1925_, 1);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_x_1925_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1929_ = v_x_1925_;
v_isShared_1930_ = v_isSharedCheck_1937_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_tail_1927_);
lean_inc(v_head_1926_);
lean_dec(v_x_1925_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1937_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
lean_inc(v_x_1923_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set_tag(v___x_1929_, 5);
lean_ctor_set(v___x_1929_, 1, v_x_1923_);
lean_ctor_set(v___x_1929_, 0, v_x_1924_);
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_x_1924_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_x_1923_);
v___x_1932_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1933_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_head_1926_);
v___x_1934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3_spec__5_spec__8(v_x_1923_, v___x_1934_, v_tail_1927_);
return v___x_1935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3(lean_object* v_x_1938_, lean_object* v_x_1939_){
_start:
{
if (lean_obj_tag(v_x_1938_) == 0)
{
lean_object* v___x_1940_; 
lean_dec(v_x_1939_);
v___x_1940_ = lean_box(0);
return v___x_1940_;
}
else
{
lean_object* v_tail_1941_; 
v_tail_1941_ = lean_ctor_get(v_x_1938_, 1);
if (lean_obj_tag(v_tail_1941_) == 0)
{
lean_object* v_head_1942_; lean_object* v___x_1943_; 
lean_dec(v_x_1939_);
v_head_1942_ = lean_ctor_get(v_x_1938_, 0);
lean_inc(v_head_1942_);
lean_dec_ref(v_x_1938_);
v___x_1943_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_head_1942_);
return v___x_1943_;
}
else
{
lean_object* v_head_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
lean_inc(v_tail_1941_);
v_head_1944_ = lean_ctor_get(v_x_1938_, 0);
lean_inc(v_head_1944_);
lean_dec_ref(v_x_1938_);
v___x_1945_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_head_1944_);
v___x_1946_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3_spec__5(v_x_1939_, v___x_1945_, v_tail_1941_);
return v___x_1946_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = ((lean_object*)(l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__2));
v___x_1952_ = lean_string_length(v___x_1951_);
return v___x_1952_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = lean_obj_once(&l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3, &l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3_once, _init_l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3);
v___x_1954_ = lean_nat_to_int(v___x_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg(lean_object* v_a_1957_){
_start:
{
if (lean_obj_tag(v_a_1957_) == 0)
{
lean_object* v___x_1958_; 
v___x_1958_ = ((lean_object*)(l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__1));
return v___x_1958_;
}
else
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; uint8_t v___x_1967_; lean_object* v___x_1968_; 
v___x_1959_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_1960_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3(v_a_1957_, v___x_1959_);
v___x_1961_ = lean_obj_once(&l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4, &l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4_once, _init_l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4);
v___x_1962_ = ((lean_object*)(l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__5));
v___x_1963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
lean_ctor_set(v___x_1963_, 1, v___x_1960_);
v___x_1964_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6));
v___x_1965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1963_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1961_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
v___x_1967_ = 0;
v___x_1968_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1968_, 0, v___x_1966_);
lean_ctor_set_uint8(v___x_1968_, sizeof(void*)*1, v___x_1967_);
return v___x_1968_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1(lean_object* v_init_1969_, lean_object* v_x_1970_){
_start:
{
if (lean_obj_tag(v_x_1970_) == 0)
{
lean_object* v_k_1971_; lean_object* v_v_1972_; lean_object* v_l_1973_; lean_object* v_r_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v_k_1971_ = lean_ctor_get(v_x_1970_, 1);
v_v_1972_ = lean_ctor_get(v_x_1970_, 2);
v_l_1973_ = lean_ctor_get(v_x_1970_, 3);
v_r_1974_ = lean_ctor_get(v_x_1970_, 4);
v___x_1975_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1(v_init_1969_, v_r_1974_);
lean_inc(v_v_1972_);
lean_inc(v_k_1971_);
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v_k_1971_);
lean_ctor_set(v___x_1976_, 1, v_v_1972_);
v___x_1977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
lean_ctor_set(v___x_1977_, 1, v___x_1975_);
v_init_1969_ = v___x_1977_;
v_x_1970_ = v_l_1973_;
goto _start;
}
else
{
return v_init_1969_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1___boxed(lean_object* v_init_1979_, lean_object* v_x_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1(v_init_1979_, v_x_1980_);
lean_dec(v_x_1980_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5_spec__8_spec__11(lean_object* v_x_1982_, lean_object* v_x_1983_, lean_object* v_x_1984_){
_start:
{
if (lean_obj_tag(v_x_1984_) == 0)
{
lean_dec(v_x_1982_);
return v_x_1983_;
}
else
{
lean_object* v_head_1985_; lean_object* v_tail_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1996_; 
v_head_1985_ = lean_ctor_get(v_x_1984_, 0);
v_tail_1986_ = lean_ctor_get(v_x_1984_, 1);
v_isSharedCheck_1996_ = !lean_is_exclusive(v_x_1984_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1988_ = v_x_1984_;
v_isShared_1989_ = v_isSharedCheck_1996_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_tail_1986_);
lean_inc(v_head_1985_);
lean_dec(v_x_1984_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1996_;
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
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_x_1983_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_x_1982_);
v___x_1991_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = l_Lean_instReprPlugin_repr___redArg(v_head_1985_);
v___x_1993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1991_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v_x_1983_ = v___x_1993_;
v_x_1984_ = v_tail_1986_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5_spec__8(lean_object* v_x_1997_, lean_object* v_x_1998_, lean_object* v_x_1999_){
_start:
{
if (lean_obj_tag(v_x_1999_) == 0)
{
lean_dec(v_x_1997_);
return v_x_1998_;
}
else
{
lean_object* v_head_2000_; lean_object* v_tail_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2011_; 
v_head_2000_ = lean_ctor_get(v_x_1999_, 0);
v_tail_2001_ = lean_ctor_get(v_x_1999_, 1);
v_isSharedCheck_2011_ = !lean_is_exclusive(v_x_1999_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2003_ = v_x_1999_;
v_isShared_2004_ = v_isSharedCheck_2011_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_tail_2001_);
lean_inc(v_head_2000_);
lean_dec(v_x_1999_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2011_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
lean_inc(v_x_1997_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set_tag(v___x_2003_, 5);
lean_ctor_set(v___x_2003_, 1, v_x_1997_);
lean_ctor_set(v___x_2003_, 0, v_x_1998_);
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_x_1998_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_x_1997_);
v___x_2006_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2007_ = l_Lean_instReprPlugin_repr___redArg(v_head_2000_);
v___x_2008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2006_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
v___x_2009_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5_spec__8_spec__11(v_x_1997_, v___x_2008_, v_tail_2001_);
return v___x_2009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5(lean_object* v_x_2012_, lean_object* v_x_2013_){
_start:
{
if (lean_obj_tag(v_x_2012_) == 0)
{
lean_object* v___x_2014_; 
lean_dec(v_x_2013_);
v___x_2014_ = lean_box(0);
return v___x_2014_;
}
else
{
lean_object* v_tail_2015_; 
v_tail_2015_ = lean_ctor_get(v_x_2012_, 1);
if (lean_obj_tag(v_tail_2015_) == 0)
{
lean_object* v_head_2016_; lean_object* v___x_2017_; 
lean_dec(v_x_2013_);
v_head_2016_ = lean_ctor_get(v_x_2012_, 0);
lean_inc(v_head_2016_);
lean_dec_ref(v_x_2012_);
v___x_2017_ = l_Lean_instReprPlugin_repr___redArg(v_head_2016_);
return v___x_2017_;
}
else
{
lean_object* v_head_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
lean_inc(v_tail_2015_);
v_head_2018_ = lean_ctor_get(v_x_2012_, 0);
lean_inc(v_head_2018_);
lean_dec_ref(v_x_2012_);
v___x_2019_ = l_Lean_instReprPlugin_repr___redArg(v_head_2018_);
v___x_2020_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5_spec__8(v_x_2013_, v___x_2019_, v_tail_2015_);
return v___x_2020_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3(lean_object* v_xs_2021_){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2022_ = lean_array_get_size(v_xs_2021_);
v___x_2023_ = lean_unsigned_to_nat(0u);
v___x_2024_ = lean_nat_dec_eq(v___x_2022_, v___x_2023_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2025_ = lean_array_to_list(v_xs_2021_);
v___x_2026_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1));
v___x_2027_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5(v___x_2025_, v___x_2026_);
v___x_2028_ = lean_obj_once(&l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4, &l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4);
v___x_2029_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5));
v___x_2030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
lean_ctor_set(v___x_2030_, 1, v___x_2027_);
v___x_2031_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6));
v___x_2032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2030_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
v___x_2033_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2028_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v___x_2034_ = l_Std_Format_fill(v___x_2033_);
return v___x_2034_;
}
else
{
lean_object* v___x_2035_; 
lean_dec_ref(v_xs_2021_);
v___x_2035_ = ((lean_object*)(l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8));
return v___x_2035_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprModuleSetup_repr_spec__0(lean_object* v_x_2036_, lean_object* v_x_2037_){
_start:
{
if (lean_obj_tag(v_x_2036_) == 0)
{
lean_object* v___x_2038_; 
v___x_2038_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__1));
return v___x_2038_;
}
else
{
lean_object* v_val_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v_val_2039_ = lean_ctor_get(v_x_2036_, 0);
lean_inc(v_val_2039_);
lean_dec_ref(v_x_2036_);
v___x_2040_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__3));
v___x_2041_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0(v_val_2039_);
v___x_2042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2040_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
v___x_2043_ = l_Repr_addAppParen(v___x_2042_, v_x_2037_);
return v___x_2043_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprModuleSetup_repr_spec__0___boxed(lean_object* v_x_2044_, lean_object* v_x_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_Option_repr___at___00Lean_instReprModuleSetup_repr_spec__0(v_x_2044_, v_x_2045_);
lean_dec(v_x_2045_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleSetup_repr___redArg(lean_object* v_x_2077_){
_start:
{
lean_object* v_name_2078_; lean_object* v_package_x3f_2079_; uint8_t v_isModule_2080_; lean_object* v_imports_x3f_2081_; lean_object* v_importArts_2082_; lean_object* v_dynlibs_2083_; lean_object* v_plugins_2084_; lean_object* v_options_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v_name_2078_ = lean_ctor_get(v_x_2077_, 0);
lean_inc(v_name_2078_);
v_package_x3f_2079_ = lean_ctor_get(v_x_2077_, 1);
lean_inc(v_package_x3f_2079_);
v_isModule_2080_ = lean_ctor_get_uint8(v_x_2077_, sizeof(void*)*7);
v_imports_x3f_2081_ = lean_ctor_get(v_x_2077_, 2);
lean_inc(v_imports_x3f_2081_);
v_importArts_2082_ = lean_ctor_get(v_x_2077_, 3);
lean_inc(v_importArts_2082_);
v_dynlibs_2083_ = lean_ctor_get(v_x_2077_, 4);
lean_inc_ref(v_dynlibs_2083_);
v_plugins_2084_ = lean_ctor_get(v_x_2077_, 5);
lean_inc_ref(v_plugins_2084_);
v_options_2085_ = lean_ctor_get(v_x_2077_, 6);
lean_inc(v_options_2085_);
lean_dec_ref(v_x_2077_);
v___x_2086_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__5));
v___x_2087_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__3));
v___x_2088_ = lean_obj_once(&l_Lean_instReprPlugin_repr___redArg___closed__4, &l_Lean_instReprPlugin_repr___redArg___closed__4_once, _init_l_Lean_instReprPlugin_repr___redArg___closed__4);
v___x_2089_ = lean_unsigned_to_nat(0u);
v___x_2090_ = l_Lean_Name_reprPrec(v_name_2078_, v___x_2089_);
v___x_2091_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2088_);
lean_ctor_set(v___x_2091_, 1, v___x_2090_);
v___x_2092_ = 0;
v___x_2093_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2093_, 0, v___x_2091_);
lean_ctor_set_uint8(v___x_2093_, sizeof(void*)*1, v___x_2092_);
v___x_2094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2087_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__9));
v___x_2096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2094_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v___x_2097_ = lean_box(1);
v___x_2098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2096_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__5));
v___x_2100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2098_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
v___x_2101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
lean_ctor_set(v___x_2101_, 1, v___x_2086_);
v___x_2102_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__7, &l_Lean_instReprModuleHeader_repr___redArg___closed__7_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__7);
v___x_2103_ = l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0(v_package_x3f_2079_, v___x_2089_);
v___x_2104_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2102_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v___x_2105_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
lean_ctor_set_uint8(v___x_2105_, sizeof(void*)*1, v___x_2092_);
v___x_2106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2101_);
lean_ctor_set(v___x_2106_, 1, v___x_2105_);
v___x_2107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
lean_ctor_set(v___x_2107_, 1, v___x_2095_);
v___x_2108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
lean_ctor_set(v___x_2108_, 1, v___x_2097_);
v___x_2109_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__6));
v___x_2110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2108_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v___x_2111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
lean_ctor_set(v___x_2111_, 1, v___x_2086_);
v___x_2112_ = l_Bool_repr___redArg(v_isModule_2080_);
v___x_2113_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2102_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
lean_ctor_set_uint8(v___x_2114_, sizeof(void*)*1, v___x_2092_);
v___x_2115_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2111_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___x_2116_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
lean_ctor_set(v___x_2116_, 1, v___x_2095_);
v___x_2117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
lean_ctor_set(v___x_2117_, 1, v___x_2097_);
v___x_2118_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__7));
v___x_2119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2117_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
v___x_2120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
lean_ctor_set(v___x_2120_, 1, v___x_2086_);
v___x_2121_ = l_Option_repr___at___00Lean_instReprModuleSetup_repr_spec__0(v_imports_x3f_2081_, v___x_2089_);
v___x_2122_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2102_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*1, v___x_2092_);
v___x_2124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2120_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
lean_ctor_set(v___x_2125_, 1, v___x_2095_);
v___x_2126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
lean_ctor_set(v___x_2126_, 1, v___x_2097_);
v___x_2127_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__9));
v___x_2128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2126_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v___x_2129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
lean_ctor_set(v___x_2129_, 1, v___x_2086_);
v___x_2130_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__15, &l_Lean_instReprImport_repr___redArg___closed__15_once, _init_l_Lean_instReprImport_repr___redArg___closed__15);
v___x_2131_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__11));
v___x_2132_ = lean_box(0);
v___x_2133_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1(v___x_2132_, v_importArts_2082_);
lean_dec(v_importArts_2082_);
v___x_2134_ = l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg(v___x_2133_);
v___x_2135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2131_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
v___x_2136_ = l_Repr_addAppParen(v___x_2135_, v___x_2089_);
v___x_2137_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2130_);
lean_ctor_set(v___x_2137_, 1, v___x_2136_);
v___x_2138_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2138_, 0, v___x_2137_);
lean_ctor_set_uint8(v___x_2138_, sizeof(void*)*1, v___x_2092_);
v___x_2139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2129_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
v___x_2140_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
lean_ctor_set(v___x_2140_, 1, v___x_2095_);
v___x_2141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2140_);
lean_ctor_set(v___x_2141_, 1, v___x_2097_);
v___x_2142_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__13));
v___x_2143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2141_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2143_);
lean_ctor_set(v___x_2144_, 1, v___x_2086_);
v___x_2145_ = lean_obj_once(&l_Lean_instReprModuleHeader_repr___redArg___closed__4, &l_Lean_instReprModuleHeader_repr___redArg___closed__4_once, _init_l_Lean_instReprModuleHeader_repr___redArg___closed__4);
v___x_2146_ = l_Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0(v_dynlibs_2083_);
v___x_2147_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2145_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
lean_ctor_set_uint8(v___x_2148_, sizeof(void*)*1, v___x_2092_);
v___x_2149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2144_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
lean_ctor_set(v___x_2150_, 1, v___x_2095_);
v___x_2151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
lean_ctor_set(v___x_2151_, 1, v___x_2097_);
v___x_2152_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__15));
v___x_2153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2151_);
lean_ctor_set(v___x_2153_, 1, v___x_2152_);
v___x_2154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
lean_ctor_set(v___x_2154_, 1, v___x_2086_);
v___x_2155_ = l_Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3(v_plugins_2084_);
v___x_2156_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2145_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
lean_ctor_set_uint8(v___x_2157_, sizeof(void*)*1, v___x_2092_);
v___x_2158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2154_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
lean_ctor_set(v___x_2159_, 1, v___x_2095_);
v___x_2160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
lean_ctor_set(v___x_2160_, 1, v___x_2097_);
v___x_2161_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__17));
v___x_2162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2160_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
lean_ctor_set(v___x_2163_, 1, v___x_2086_);
v___x_2164_ = l_Lean_instReprLeanOptions_repr___redArg(v_options_2085_);
lean_dec(v_options_2085_);
v___x_2165_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2145_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
lean_ctor_set_uint8(v___x_2166_, sizeof(void*)*1, v___x_2092_);
v___x_2167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2163_);
lean_ctor_set(v___x_2167_, 1, v___x_2166_);
v___x_2168_ = lean_obj_once(&l_Lean_instReprImport_repr___redArg___closed__20, &l_Lean_instReprImport_repr___redArg___closed__20_once, _init_l_Lean_instReprImport_repr___redArg___closed__20);
v___x_2169_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__21));
v___x_2170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2169_);
lean_ctor_set(v___x_2170_, 1, v___x_2167_);
v___x_2171_ = ((lean_object*)(l_Lean_instReprImport_repr___redArg___closed__22));
v___x_2172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2170_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
v___x_2173_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2168_);
lean_ctor_set(v___x_2173_, 1, v___x_2172_);
v___x_2174_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
lean_ctor_set_uint8(v___x_2174_, sizeof(void*)*1, v___x_2092_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleSetup_repr(lean_object* v_x_2175_, lean_object* v_prec_2176_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Lean_instReprModuleSetup_repr___redArg(v_x_2175_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprModuleSetup_repr___boxed(lean_object* v_x_2178_, lean_object* v_prec_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Lean_instReprModuleSetup_repr(v_x_2178_, v_prec_2179_);
lean_dec(v_prec_2179_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2(lean_object* v_a_2181_, lean_object* v_n_2182_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg(v_a_2181_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___boxed(lean_object* v_a_2184_, lean_object* v_n_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2(v_a_2184_, v_n_2185_);
lean_dec(v_n_2185_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2(lean_object* v_x_2187_, lean_object* v_x_2188_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_x_2187_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___boxed(lean_object* v_x_2190_, lean_object* v_x_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2(v_x_2190_, v_x_2191_);
lean_dec(v_x_2191_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__6(size_t v_sz_2203_, size_t v_i_2204_, lean_object* v_bs_2205_){
_start:
{
uint8_t v___x_2206_; 
v___x_2206_ = lean_usize_dec_lt(v_i_2204_, v_sz_2203_);
if (v___x_2206_ == 0)
{
return v_bs_2205_;
}
else
{
lean_object* v_v_2207_; lean_object* v___x_2208_; lean_object* v_bs_x27_2209_; lean_object* v___x_2210_; size_t v___x_2211_; size_t v___x_2212_; lean_object* v___x_2213_; 
v_v_2207_ = lean_array_uget(v_bs_2205_, v_i_2204_);
v___x_2208_ = lean_unsigned_to_nat(0u);
v_bs_x27_2209_ = lean_array_uset(v_bs_2205_, v_i_2204_, v___x_2208_);
v___x_2210_ = l_Lean_instToJsonPlugin_toJson(v_v_2207_);
v___x_2211_ = ((size_t)1ULL);
v___x_2212_ = lean_usize_add(v_i_2204_, v___x_2211_);
v___x_2213_ = lean_array_uset(v_bs_x27_2209_, v_i_2204_, v___x_2210_);
v_i_2204_ = v___x_2212_;
v_bs_2205_ = v___x_2213_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__6___boxed(lean_object* v_sz_2215_, lean_object* v_i_2216_, lean_object* v_bs_2217_){
_start:
{
size_t v_sz_boxed_2218_; size_t v_i_boxed_2219_; lean_object* v_res_2220_; 
v_sz_boxed_2218_ = lean_unbox_usize(v_sz_2215_);
lean_dec(v_sz_2215_);
v_i_boxed_2219_ = lean_unbox_usize(v_i_2216_);
lean_dec(v_i_2216_);
v_res_2220_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__6(v_sz_boxed_2218_, v_i_boxed_2219_, v_bs_2217_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3(lean_object* v_a_2221_){
_start:
{
size_t v_sz_2222_; size_t v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v_sz_2222_ = lean_array_size(v_a_2221_);
v___x_2223_ = ((size_t)0ULL);
v___x_2224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__6(v_sz_2222_, v___x_2223_, v_a_2221_);
v___x_2225_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2___redArg(lean_object* v_msg_2226_){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = lean_box(1);
v___x_2228_ = lean_panic_fn_borrowed(v___x_2227_, v_msg_2226_);
return v___x_2228_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2232_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__2));
v___x_2233_ = lean_unsigned_to_nat(35u);
v___x_2234_ = lean_unsigned_to_nat(276u);
v___x_2235_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__1));
v___x_2236_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__0));
v___x_2237_ = l_mkPanicMessageWithDecl(v___x_2236_, v___x_2235_, v___x_2234_, v___x_2233_, v___x_2232_);
return v___x_2237_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2238_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__2));
v___x_2239_ = lean_unsigned_to_nat(21u);
v___x_2240_ = lean_unsigned_to_nat(277u);
v___x_2241_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__1));
v___x_2242_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__0));
v___x_2243_ = l_mkPanicMessageWithDecl(v___x_2242_, v___x_2241_, v___x_2240_, v___x_2239_, v___x_2238_);
return v___x_2243_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__7(void){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2246_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__6));
v___x_2247_ = lean_unsigned_to_nat(35u);
v___x_2248_ = lean_unsigned_to_nat(182u);
v___x_2249_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__5));
v___x_2250_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__0));
v___x_2251_ = l_mkPanicMessageWithDecl(v___x_2250_, v___x_2249_, v___x_2248_, v___x_2247_, v___x_2246_);
return v___x_2251_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2252_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__6));
v___x_2253_ = lean_unsigned_to_nat(21u);
v___x_2254_ = lean_unsigned_to_nat(183u);
v___x_2255_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__5));
v___x_2256_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__0));
v___x_2257_ = l_mkPanicMessageWithDecl(v___x_2256_, v___x_2255_, v___x_2254_, v___x_2253_, v___x_2252_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg(lean_object* v_k_2258_, lean_object* v_v_2259_, lean_object* v_t_2260_){
_start:
{
if (lean_obj_tag(v_t_2260_) == 0)
{
lean_object* v_size_2261_; lean_object* v_k_2262_; lean_object* v_v_2263_; lean_object* v_l_2264_; lean_object* v_r_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2622_; 
v_size_2261_ = lean_ctor_get(v_t_2260_, 0);
v_k_2262_ = lean_ctor_get(v_t_2260_, 1);
v_v_2263_ = lean_ctor_get(v_t_2260_, 2);
v_l_2264_ = lean_ctor_get(v_t_2260_, 3);
v_r_2265_ = lean_ctor_get(v_t_2260_, 4);
v_isSharedCheck_2622_ = !lean_is_exclusive(v_t_2260_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2267_ = v_t_2260_;
v_isShared_2268_ = v_isSharedCheck_2622_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_r_2265_);
lean_inc(v_l_2264_);
lean_inc(v_v_2263_);
lean_inc(v_k_2262_);
lean_inc(v_size_2261_);
lean_dec(v_t_2260_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2622_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
uint8_t v___x_2269_; 
v___x_2269_ = lean_string_dec_lt(v_k_2258_, v_k_2262_);
if (v___x_2269_ == 0)
{
uint8_t v___x_2270_; 
v___x_2270_ = lean_string_dec_eq(v_k_2258_, v_k_2262_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; 
lean_dec(v_size_2261_);
v___x_2271_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg(v_k_2258_, v_v_2259_, v_r_2265_);
if (lean_obj_tag(v_l_2264_) == 0)
{
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_size_2272_; lean_object* v_size_2273_; lean_object* v_k_2274_; lean_object* v_v_2275_; lean_object* v_l_2276_; lean_object* v_r_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; uint8_t v___x_2280_; 
v_size_2272_ = lean_ctor_get(v_l_2264_, 0);
v_size_2273_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_size_2273_);
v_k_2274_ = lean_ctor_get(v___x_2271_, 1);
lean_inc(v_k_2274_);
v_v_2275_ = lean_ctor_get(v___x_2271_, 2);
lean_inc(v_v_2275_);
v_l_2276_ = lean_ctor_get(v___x_2271_, 3);
lean_inc(v_l_2276_);
v_r_2277_ = lean_ctor_get(v___x_2271_, 4);
lean_inc(v_r_2277_);
v___x_2278_ = lean_unsigned_to_nat(3u);
v___x_2279_ = lean_nat_mul(v___x_2278_, v_size_2272_);
v___x_2280_ = lean_nat_dec_lt(v___x_2279_, v_size_2273_);
lean_dec(v___x_2279_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2285_; 
lean_dec(v_r_2277_);
lean_dec(v_l_2276_);
lean_dec(v_v_2275_);
lean_dec(v_k_2274_);
v___x_2281_ = lean_unsigned_to_nat(1u);
v___x_2282_ = lean_nat_add(v___x_2281_, v_size_2272_);
v___x_2283_ = lean_nat_add(v___x_2282_, v_size_2273_);
lean_dec(v_size_2273_);
lean_dec(v___x_2282_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v___x_2271_);
lean_ctor_set(v___x_2267_, 0, v___x_2283_);
v___x_2285_ = v___x_2267_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2283_);
lean_ctor_set(v_reuseFailAlloc_2286_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2286_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2286_, 3, v_l_2264_);
lean_ctor_set(v_reuseFailAlloc_2286_, 4, v___x_2271_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
else
{
lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2356_; 
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2356_ == 0)
{
lean_object* v_unused_2357_; lean_object* v_unused_2358_; lean_object* v_unused_2359_; lean_object* v_unused_2360_; lean_object* v_unused_2361_; 
v_unused_2357_ = lean_ctor_get(v___x_2271_, 4);
lean_dec(v_unused_2357_);
v_unused_2358_ = lean_ctor_get(v___x_2271_, 3);
lean_dec(v_unused_2358_);
v_unused_2359_ = lean_ctor_get(v___x_2271_, 2);
lean_dec(v_unused_2359_);
v_unused_2360_ = lean_ctor_get(v___x_2271_, 1);
lean_dec(v_unused_2360_);
v_unused_2361_ = lean_ctor_get(v___x_2271_, 0);
lean_dec(v_unused_2361_);
v___x_2288_ = v___x_2271_;
v_isShared_2289_ = v_isSharedCheck_2356_;
goto v_resetjp_2287_;
}
else
{
lean_dec(v___x_2271_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2356_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
if (lean_obj_tag(v_l_2276_) == 0)
{
if (lean_obj_tag(v_r_2277_) == 0)
{
lean_object* v_size_2290_; lean_object* v_k_2291_; lean_object* v_v_2292_; lean_object* v_l_2293_; lean_object* v_r_2294_; lean_object* v_size_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; uint8_t v___x_2298_; 
v_size_2290_ = lean_ctor_get(v_l_2276_, 0);
v_k_2291_ = lean_ctor_get(v_l_2276_, 1);
v_v_2292_ = lean_ctor_get(v_l_2276_, 2);
v_l_2293_ = lean_ctor_get(v_l_2276_, 3);
v_r_2294_ = lean_ctor_get(v_l_2276_, 4);
v_size_2295_ = lean_ctor_get(v_r_2277_, 0);
v___x_2296_ = lean_unsigned_to_nat(2u);
v___x_2297_ = lean_nat_mul(v___x_2296_, v_size_2295_);
v___x_2298_ = lean_nat_dec_lt(v_size_2290_, v___x_2297_);
lean_dec(v___x_2297_);
if (v___x_2298_ == 0)
{
lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2327_; 
lean_inc(v_r_2294_);
lean_inc(v_l_2293_);
lean_inc(v_v_2292_);
lean_inc(v_k_2291_);
v_isSharedCheck_2327_ = !lean_is_exclusive(v_l_2276_);
if (v_isSharedCheck_2327_ == 0)
{
lean_object* v_unused_2328_; lean_object* v_unused_2329_; lean_object* v_unused_2330_; lean_object* v_unused_2331_; lean_object* v_unused_2332_; 
v_unused_2328_ = lean_ctor_get(v_l_2276_, 4);
lean_dec(v_unused_2328_);
v_unused_2329_ = lean_ctor_get(v_l_2276_, 3);
lean_dec(v_unused_2329_);
v_unused_2330_ = lean_ctor_get(v_l_2276_, 2);
lean_dec(v_unused_2330_);
v_unused_2331_ = lean_ctor_get(v_l_2276_, 1);
lean_dec(v_unused_2331_);
v_unused_2332_ = lean_ctor_get(v_l_2276_, 0);
lean_dec(v_unused_2332_);
v___x_2300_ = v_l_2276_;
v_isShared_2301_ = v_isSharedCheck_2327_;
goto v_resetjp_2299_;
}
else
{
lean_dec(v_l_2276_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2327_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2317_; 
v___x_2302_ = lean_unsigned_to_nat(1u);
v___x_2303_ = lean_nat_add(v___x_2302_, v_size_2272_);
v___x_2304_ = lean_nat_add(v___x_2303_, v_size_2273_);
lean_dec(v_size_2273_);
if (lean_obj_tag(v_l_2293_) == 0)
{
lean_object* v_size_2325_; 
v_size_2325_ = lean_ctor_get(v_l_2293_, 0);
lean_inc(v_size_2325_);
v___y_2317_ = v_size_2325_;
goto v___jp_2316_;
}
else
{
lean_object* v___x_2326_; 
v___x_2326_ = lean_unsigned_to_nat(0u);
v___y_2317_ = v___x_2326_;
goto v___jp_2316_;
}
v___jp_2305_:
{
lean_object* v___x_2309_; lean_object* v___x_2311_; 
v___x_2309_ = lean_nat_add(v___y_2306_, v___y_2308_);
lean_dec(v___y_2308_);
lean_dec(v___y_2306_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 4, v_r_2277_);
lean_ctor_set(v___x_2300_, 3, v_r_2294_);
lean_ctor_set(v___x_2300_, 2, v_v_2275_);
lean_ctor_set(v___x_2300_, 1, v_k_2274_);
lean_ctor_set(v___x_2300_, 0, v___x_2309_);
v___x_2311_ = v___x_2300_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v___x_2309_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v_k_2274_);
lean_ctor_set(v_reuseFailAlloc_2315_, 2, v_v_2275_);
lean_ctor_set(v_reuseFailAlloc_2315_, 3, v_r_2294_);
lean_ctor_set(v_reuseFailAlloc_2315_, 4, v_r_2277_);
v___x_2311_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
lean_object* v___x_2313_; 
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 4, v___x_2311_);
lean_ctor_set(v___x_2288_, 3, v___y_2307_);
lean_ctor_set(v___x_2288_, 2, v_v_2292_);
lean_ctor_set(v___x_2288_, 1, v_k_2291_);
lean_ctor_set(v___x_2288_, 0, v___x_2304_);
v___x_2313_ = v___x_2288_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_k_2291_);
lean_ctor_set(v_reuseFailAlloc_2314_, 2, v_v_2292_);
lean_ctor_set(v_reuseFailAlloc_2314_, 3, v___y_2307_);
lean_ctor_set(v_reuseFailAlloc_2314_, 4, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
v___jp_2316_:
{
lean_object* v___x_2318_; lean_object* v___x_2320_; 
v___x_2318_ = lean_nat_add(v___x_2303_, v___y_2317_);
lean_dec(v___y_2317_);
lean_dec(v___x_2303_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v_l_2293_);
lean_ctor_set(v___x_2267_, 0, v___x_2318_);
v___x_2320_ = v___x_2267_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2324_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2324_, 3, v_l_2264_);
lean_ctor_set(v_reuseFailAlloc_2324_, 4, v_l_2293_);
v___x_2320_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2321_; 
v___x_2321_ = lean_nat_add(v___x_2302_, v_size_2295_);
if (lean_obj_tag(v_r_2294_) == 0)
{
lean_object* v_size_2322_; 
v_size_2322_ = lean_ctor_get(v_r_2294_, 0);
lean_inc(v_size_2322_);
v___y_2306_ = v___x_2321_;
v___y_2307_ = v___x_2320_;
v___y_2308_ = v_size_2322_;
goto v___jp_2305_;
}
else
{
lean_object* v___x_2323_; 
v___x_2323_ = lean_unsigned_to_nat(0u);
v___y_2306_ = v___x_2321_;
v___y_2307_ = v___x_2320_;
v___y_2308_ = v___x_2323_;
goto v___jp_2305_;
}
}
}
}
}
else
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2338_; 
lean_del_object(v___x_2267_);
v___x_2333_ = lean_unsigned_to_nat(1u);
v___x_2334_ = lean_nat_add(v___x_2333_, v_size_2272_);
v___x_2335_ = lean_nat_add(v___x_2334_, v_size_2273_);
lean_dec(v_size_2273_);
v___x_2336_ = lean_nat_add(v___x_2334_, v_size_2290_);
lean_dec(v___x_2334_);
lean_inc_ref(v_l_2264_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 4, v_l_2276_);
lean_ctor_set(v___x_2288_, 3, v_l_2264_);
lean_ctor_set(v___x_2288_, 2, v_v_2263_);
lean_ctor_set(v___x_2288_, 1, v_k_2262_);
lean_ctor_set(v___x_2288_, 0, v___x_2336_);
v___x_2338_ = v___x_2288_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2336_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2351_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2351_, 3, v_l_2264_);
lean_ctor_set(v_reuseFailAlloc_2351_, 4, v_l_2276_);
v___x_2338_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
v_isSharedCheck_2345_ = !lean_is_exclusive(v_l_2264_);
if (v_isSharedCheck_2345_ == 0)
{
lean_object* v_unused_2346_; lean_object* v_unused_2347_; lean_object* v_unused_2348_; lean_object* v_unused_2349_; lean_object* v_unused_2350_; 
v_unused_2346_ = lean_ctor_get(v_l_2264_, 4);
lean_dec(v_unused_2346_);
v_unused_2347_ = lean_ctor_get(v_l_2264_, 3);
lean_dec(v_unused_2347_);
v_unused_2348_ = lean_ctor_get(v_l_2264_, 2);
lean_dec(v_unused_2348_);
v_unused_2349_ = lean_ctor_get(v_l_2264_, 1);
lean_dec(v_unused_2349_);
v_unused_2350_ = lean_ctor_get(v_l_2264_, 0);
lean_dec(v_unused_2350_);
v___x_2340_ = v_l_2264_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_dec(v_l_2264_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 4, v_r_2277_);
lean_ctor_set(v___x_2340_, 3, v___x_2338_);
lean_ctor_set(v___x_2340_, 2, v_v_2275_);
lean_ctor_set(v___x_2340_, 1, v_k_2274_);
lean_ctor_set(v___x_2340_, 0, v___x_2335_);
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2335_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_k_2274_);
lean_ctor_set(v_reuseFailAlloc_2344_, 2, v_v_2275_);
lean_ctor_set(v_reuseFailAlloc_2344_, 3, v___x_2338_);
lean_ctor_set(v_reuseFailAlloc_2344_, 4, v_r_2277_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
}
else
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
lean_dec_ref(v_l_2276_);
lean_del_object(v___x_2288_);
lean_dec(v_v_2275_);
lean_dec(v_k_2274_);
lean_dec(v_size_2273_);
lean_dec_ref(v_l_2264_);
lean_del_object(v___x_2267_);
lean_dec(v_v_2263_);
lean_dec(v_k_2262_);
v___x_2352_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__3);
v___x_2353_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2___redArg(v___x_2352_);
return v___x_2353_;
}
}
else
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
lean_del_object(v___x_2288_);
lean_dec(v_r_2277_);
lean_dec(v_v_2275_);
lean_dec(v_k_2274_);
lean_dec(v_size_2273_);
lean_dec_ref(v_l_2264_);
lean_del_object(v___x_2267_);
lean_dec(v_v_2263_);
lean_dec(v_k_2262_);
v___x_2354_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__4);
v___x_2355_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2___redArg(v___x_2354_);
return v___x_2355_;
}
}
}
}
else
{
lean_object* v_size_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2366_; 
v_size_2362_ = lean_ctor_get(v_l_2264_, 0);
v___x_2363_ = lean_unsigned_to_nat(1u);
v___x_2364_ = lean_nat_add(v___x_2363_, v_size_2362_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v___x_2271_);
lean_ctor_set(v___x_2267_, 0, v___x_2364_);
v___x_2366_ = v___x_2267_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2364_);
lean_ctor_set(v_reuseFailAlloc_2367_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2367_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2367_, 3, v_l_2264_);
lean_ctor_set(v_reuseFailAlloc_2367_, 4, v___x_2271_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
else
{
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_l_2368_; 
v_l_2368_ = lean_ctor_get(v___x_2271_, 3);
lean_inc(v_l_2368_);
if (lean_obj_tag(v_l_2368_) == 0)
{
lean_object* v_r_2369_; 
v_r_2369_ = lean_ctor_get(v___x_2271_, 4);
lean_inc(v_r_2369_);
if (lean_obj_tag(v_r_2369_) == 0)
{
lean_object* v_size_2370_; lean_object* v_k_2371_; lean_object* v_v_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2386_; 
v_size_2370_ = lean_ctor_get(v___x_2271_, 0);
v_k_2371_ = lean_ctor_get(v___x_2271_, 1);
v_v_2372_ = lean_ctor_get(v___x_2271_, 2);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2386_ == 0)
{
lean_object* v_unused_2387_; lean_object* v_unused_2388_; 
v_unused_2387_ = lean_ctor_get(v___x_2271_, 4);
lean_dec(v_unused_2387_);
v_unused_2388_ = lean_ctor_get(v___x_2271_, 3);
lean_dec(v_unused_2388_);
v___x_2374_ = v___x_2271_;
v_isShared_2375_ = v_isSharedCheck_2386_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_v_2372_);
lean_inc(v_k_2371_);
lean_inc(v_size_2370_);
lean_dec(v___x_2271_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2386_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v_size_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2381_; 
v_size_2376_ = lean_ctor_get(v_l_2368_, 0);
v___x_2377_ = lean_unsigned_to_nat(1u);
v___x_2378_ = lean_nat_add(v___x_2377_, v_size_2370_);
lean_dec(v_size_2370_);
v___x_2379_ = lean_nat_add(v___x_2377_, v_size_2376_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 4, v_l_2368_);
lean_ctor_set(v___x_2374_, 3, v_l_2264_);
lean_ctor_set(v___x_2374_, 2, v_v_2263_);
lean_ctor_set(v___x_2374_, 1, v_k_2262_);
lean_ctor_set(v___x_2374_, 0, v___x_2379_);
v___x_2381_ = v___x_2374_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2379_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2385_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2385_, 3, v_l_2264_);
lean_ctor_set(v_reuseFailAlloc_2385_, 4, v_l_2368_);
v___x_2381_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
lean_object* v___x_2383_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v_r_2369_);
lean_ctor_set(v___x_2267_, 3, v___x_2381_);
lean_ctor_set(v___x_2267_, 2, v_v_2372_);
lean_ctor_set(v___x_2267_, 1, v_k_2371_);
lean_ctor_set(v___x_2267_, 0, v___x_2378_);
v___x_2383_ = v___x_2267_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2378_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v_k_2371_);
lean_ctor_set(v_reuseFailAlloc_2384_, 2, v_v_2372_);
lean_ctor_set(v_reuseFailAlloc_2384_, 3, v___x_2381_);
lean_ctor_set(v_reuseFailAlloc_2384_, 4, v_r_2369_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
else
{
lean_object* v_k_2389_; lean_object* v_v_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2414_; 
v_k_2389_ = lean_ctor_get(v___x_2271_, 1);
v_v_2390_ = lean_ctor_get(v___x_2271_, 2);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2414_ == 0)
{
lean_object* v_unused_2415_; lean_object* v_unused_2416_; lean_object* v_unused_2417_; 
v_unused_2415_ = lean_ctor_get(v___x_2271_, 4);
lean_dec(v_unused_2415_);
v_unused_2416_ = lean_ctor_get(v___x_2271_, 3);
lean_dec(v_unused_2416_);
v_unused_2417_ = lean_ctor_get(v___x_2271_, 0);
lean_dec(v_unused_2417_);
v___x_2392_ = v___x_2271_;
v_isShared_2393_ = v_isSharedCheck_2414_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_v_2390_);
lean_inc(v_k_2389_);
lean_dec(v___x_2271_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2414_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v_k_2394_; lean_object* v_v_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2410_; 
v_k_2394_ = lean_ctor_get(v_l_2368_, 1);
v_v_2395_ = lean_ctor_get(v_l_2368_, 2);
v_isSharedCheck_2410_ = !lean_is_exclusive(v_l_2368_);
if (v_isSharedCheck_2410_ == 0)
{
lean_object* v_unused_2411_; lean_object* v_unused_2412_; lean_object* v_unused_2413_; 
v_unused_2411_ = lean_ctor_get(v_l_2368_, 4);
lean_dec(v_unused_2411_);
v_unused_2412_ = lean_ctor_get(v_l_2368_, 3);
lean_dec(v_unused_2412_);
v_unused_2413_ = lean_ctor_get(v_l_2368_, 0);
lean_dec(v_unused_2413_);
v___x_2397_ = v_l_2368_;
v_isShared_2398_ = v_isSharedCheck_2410_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_v_2395_);
lean_inc(v_k_2394_);
lean_dec(v_l_2368_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2410_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2402_; 
v___x_2399_ = lean_unsigned_to_nat(3u);
v___x_2400_ = lean_unsigned_to_nat(1u);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 4, v_r_2369_);
lean_ctor_set(v___x_2397_, 3, v_r_2369_);
lean_ctor_set(v___x_2397_, 2, v_v_2263_);
lean_ctor_set(v___x_2397_, 1, v_k_2262_);
lean_ctor_set(v___x_2397_, 0, v___x_2400_);
v___x_2402_ = v___x_2397_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2400_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2409_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2409_, 3, v_r_2369_);
lean_ctor_set(v_reuseFailAlloc_2409_, 4, v_r_2369_);
v___x_2402_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
lean_object* v___x_2404_; 
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 3, v_r_2369_);
lean_ctor_set(v___x_2392_, 0, v___x_2400_);
v___x_2404_ = v___x_2392_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2400_);
lean_ctor_set(v_reuseFailAlloc_2408_, 1, v_k_2389_);
lean_ctor_set(v_reuseFailAlloc_2408_, 2, v_v_2390_);
lean_ctor_set(v_reuseFailAlloc_2408_, 3, v_r_2369_);
lean_ctor_set(v_reuseFailAlloc_2408_, 4, v_r_2369_);
v___x_2404_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
lean_object* v___x_2406_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v___x_2404_);
lean_ctor_set(v___x_2267_, 3, v___x_2402_);
lean_ctor_set(v___x_2267_, 2, v_v_2395_);
lean_ctor_set(v___x_2267_, 1, v_k_2394_);
lean_ctor_set(v___x_2267_, 0, v___x_2399_);
v___x_2406_ = v___x_2267_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2399_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v_k_2394_);
lean_ctor_set(v_reuseFailAlloc_2407_, 2, v_v_2395_);
lean_ctor_set(v_reuseFailAlloc_2407_, 3, v___x_2402_);
lean_ctor_set(v_reuseFailAlloc_2407_, 4, v___x_2404_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_2418_; 
v_r_2418_ = lean_ctor_get(v___x_2271_, 4);
lean_inc(v_r_2418_);
if (lean_obj_tag(v_r_2418_) == 0)
{
lean_object* v_k_2419_; lean_object* v_v_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2432_; 
v_k_2419_ = lean_ctor_get(v___x_2271_, 1);
v_v_2420_ = lean_ctor_get(v___x_2271_, 2);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2432_ == 0)
{
lean_object* v_unused_2433_; lean_object* v_unused_2434_; lean_object* v_unused_2435_; 
v_unused_2433_ = lean_ctor_get(v___x_2271_, 4);
lean_dec(v_unused_2433_);
v_unused_2434_ = lean_ctor_get(v___x_2271_, 3);
lean_dec(v_unused_2434_);
v_unused_2435_ = lean_ctor_get(v___x_2271_, 0);
lean_dec(v_unused_2435_);
v___x_2422_ = v___x_2271_;
v_isShared_2423_ = v_isSharedCheck_2432_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_v_2420_);
lean_inc(v_k_2419_);
lean_dec(v___x_2271_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2432_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2427_; 
v___x_2424_ = lean_unsigned_to_nat(3u);
v___x_2425_ = lean_unsigned_to_nat(1u);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 4, v_l_2368_);
lean_ctor_set(v___x_2422_, 2, v_v_2263_);
lean_ctor_set(v___x_2422_, 1, v_k_2262_);
lean_ctor_set(v___x_2422_, 0, v___x_2425_);
v___x_2427_ = v___x_2422_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2425_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2431_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2431_, 3, v_l_2368_);
lean_ctor_set(v_reuseFailAlloc_2431_, 4, v_l_2368_);
v___x_2427_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
lean_object* v___x_2429_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v_r_2418_);
lean_ctor_set(v___x_2267_, 3, v___x_2427_);
lean_ctor_set(v___x_2267_, 2, v_v_2420_);
lean_ctor_set(v___x_2267_, 1, v_k_2419_);
lean_ctor_set(v___x_2267_, 0, v___x_2424_);
v___x_2429_ = v___x_2267_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2424_);
lean_ctor_set(v_reuseFailAlloc_2430_, 1, v_k_2419_);
lean_ctor_set(v_reuseFailAlloc_2430_, 2, v_v_2420_);
lean_ctor_set(v_reuseFailAlloc_2430_, 3, v___x_2427_);
lean_ctor_set(v_reuseFailAlloc_2430_, 4, v_r_2418_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
else
{
lean_object* v___x_2436_; lean_object* v___x_2438_; 
v___x_2436_ = lean_unsigned_to_nat(2u);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v___x_2271_);
lean_ctor_set(v___x_2267_, 3, v_r_2418_);
lean_ctor_set(v___x_2267_, 0, v___x_2436_);
v___x_2438_ = v___x_2267_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2436_);
lean_ctor_set(v_reuseFailAlloc_2439_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2439_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2439_, 3, v_r_2418_);
lean_ctor_set(v_reuseFailAlloc_2439_, 4, v___x_2271_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
else
{
lean_object* v___x_2440_; lean_object* v___x_2442_; 
v___x_2440_ = lean_unsigned_to_nat(1u);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v___x_2271_);
lean_ctor_set(v___x_2267_, 3, v___x_2271_);
lean_ctor_set(v___x_2267_, 0, v___x_2440_);
v___x_2442_ = v___x_2267_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2440_);
lean_ctor_set(v_reuseFailAlloc_2443_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2443_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2443_, 3, v___x_2271_);
lean_ctor_set(v_reuseFailAlloc_2443_, 4, v___x_2271_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
else
{
lean_object* v___x_2445_; 
lean_dec(v_v_2263_);
lean_dec(v_k_2262_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 2, v_v_2259_);
lean_ctor_set(v___x_2267_, 1, v_k_2258_);
v___x_2445_ = v___x_2267_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_size_2261_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v_k_2258_);
lean_ctor_set(v_reuseFailAlloc_2446_, 2, v_v_2259_);
lean_ctor_set(v_reuseFailAlloc_2446_, 3, v_l_2264_);
lean_ctor_set(v_reuseFailAlloc_2446_, 4, v_r_2265_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
else
{
lean_object* v___x_2447_; 
lean_dec(v_size_2261_);
v___x_2447_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg(v_k_2258_, v_v_2259_, v_l_2264_);
if (lean_obj_tag(v_r_2265_) == 0)
{
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_size_2448_; lean_object* v_size_2449_; lean_object* v_k_2450_; lean_object* v_v_2451_; lean_object* v_l_2452_; lean_object* v_r_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; uint8_t v___x_2456_; 
v_size_2448_ = lean_ctor_get(v_r_2265_, 0);
v_size_2449_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_size_2449_);
v_k_2450_ = lean_ctor_get(v___x_2447_, 1);
lean_inc(v_k_2450_);
v_v_2451_ = lean_ctor_get(v___x_2447_, 2);
lean_inc(v_v_2451_);
v_l_2452_ = lean_ctor_get(v___x_2447_, 3);
lean_inc(v_l_2452_);
v_r_2453_ = lean_ctor_get(v___x_2447_, 4);
lean_inc(v_r_2453_);
v___x_2454_ = lean_unsigned_to_nat(3u);
v___x_2455_ = lean_nat_mul(v___x_2454_, v_size_2448_);
v___x_2456_ = lean_nat_dec_lt(v___x_2455_, v_size_2449_);
lean_dec(v___x_2455_);
if (v___x_2456_ == 0)
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2461_; 
lean_dec(v_r_2453_);
lean_dec(v_l_2452_);
lean_dec(v_v_2451_);
lean_dec(v_k_2450_);
v___x_2457_ = lean_unsigned_to_nat(1u);
v___x_2458_ = lean_nat_add(v___x_2457_, v_size_2449_);
lean_dec(v_size_2449_);
v___x_2459_ = lean_nat_add(v___x_2458_, v_size_2448_);
lean_dec(v___x_2458_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 3, v___x_2447_);
lean_ctor_set(v___x_2267_, 0, v___x_2459_);
v___x_2461_ = v___x_2267_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2459_);
lean_ctor_set(v_reuseFailAlloc_2462_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2462_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2462_, 3, v___x_2447_);
lean_ctor_set(v_reuseFailAlloc_2462_, 4, v_r_2265_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
else
{
lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2534_; 
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2534_ == 0)
{
lean_object* v_unused_2535_; lean_object* v_unused_2536_; lean_object* v_unused_2537_; lean_object* v_unused_2538_; lean_object* v_unused_2539_; 
v_unused_2535_ = lean_ctor_get(v___x_2447_, 4);
lean_dec(v_unused_2535_);
v_unused_2536_ = lean_ctor_get(v___x_2447_, 3);
lean_dec(v_unused_2536_);
v_unused_2537_ = lean_ctor_get(v___x_2447_, 2);
lean_dec(v_unused_2537_);
v_unused_2538_ = lean_ctor_get(v___x_2447_, 1);
lean_dec(v_unused_2538_);
v_unused_2539_ = lean_ctor_get(v___x_2447_, 0);
lean_dec(v_unused_2539_);
v___x_2464_ = v___x_2447_;
v_isShared_2465_ = v_isSharedCheck_2534_;
goto v_resetjp_2463_;
}
else
{
lean_dec(v___x_2447_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2534_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
if (lean_obj_tag(v_l_2452_) == 0)
{
if (lean_obj_tag(v_r_2453_) == 0)
{
lean_object* v_size_2466_; lean_object* v_size_2467_; lean_object* v_k_2468_; lean_object* v_v_2469_; lean_object* v_l_2470_; lean_object* v_r_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; uint8_t v___x_2474_; 
v_size_2466_ = lean_ctor_get(v_l_2452_, 0);
v_size_2467_ = lean_ctor_get(v_r_2453_, 0);
v_k_2468_ = lean_ctor_get(v_r_2453_, 1);
v_v_2469_ = lean_ctor_get(v_r_2453_, 2);
v_l_2470_ = lean_ctor_get(v_r_2453_, 3);
v_r_2471_ = lean_ctor_get(v_r_2453_, 4);
v___x_2472_ = lean_unsigned_to_nat(2u);
v___x_2473_ = lean_nat_mul(v___x_2472_, v_size_2466_);
v___x_2474_ = lean_nat_dec_lt(v_size_2467_, v___x_2473_);
lean_dec(v___x_2473_);
if (v___x_2474_ == 0)
{
lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2504_; 
lean_inc(v_r_2471_);
lean_inc(v_l_2470_);
lean_inc(v_v_2469_);
lean_inc(v_k_2468_);
v_isSharedCheck_2504_ = !lean_is_exclusive(v_r_2453_);
if (v_isSharedCheck_2504_ == 0)
{
lean_object* v_unused_2505_; lean_object* v_unused_2506_; lean_object* v_unused_2507_; lean_object* v_unused_2508_; lean_object* v_unused_2509_; 
v_unused_2505_ = lean_ctor_get(v_r_2453_, 4);
lean_dec(v_unused_2505_);
v_unused_2506_ = lean_ctor_get(v_r_2453_, 3);
lean_dec(v_unused_2506_);
v_unused_2507_ = lean_ctor_get(v_r_2453_, 2);
lean_dec(v_unused_2507_);
v_unused_2508_ = lean_ctor_get(v_r_2453_, 1);
lean_dec(v_unused_2508_);
v_unused_2509_ = lean_ctor_get(v_r_2453_, 0);
lean_dec(v_unused_2509_);
v___x_2476_ = v_r_2453_;
v_isShared_2477_ = v_isSharedCheck_2504_;
goto v_resetjp_2475_;
}
else
{
lean_dec(v_r_2453_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2504_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___x_2492_; lean_object* v___y_2494_; 
v___x_2478_ = lean_unsigned_to_nat(1u);
v___x_2479_ = lean_nat_add(v___x_2478_, v_size_2449_);
lean_dec(v_size_2449_);
v___x_2480_ = lean_nat_add(v___x_2479_, v_size_2448_);
lean_dec(v___x_2479_);
v___x_2492_ = lean_nat_add(v___x_2478_, v_size_2466_);
if (lean_obj_tag(v_l_2470_) == 0)
{
lean_object* v_size_2502_; 
v_size_2502_ = lean_ctor_get(v_l_2470_, 0);
lean_inc(v_size_2502_);
v___y_2494_ = v_size_2502_;
goto v___jp_2493_;
}
else
{
lean_object* v___x_2503_; 
v___x_2503_ = lean_unsigned_to_nat(0u);
v___y_2494_ = v___x_2503_;
goto v___jp_2493_;
}
v___jp_2481_:
{
lean_object* v___x_2485_; lean_object* v___x_2487_; 
v___x_2485_ = lean_nat_add(v___y_2482_, v___y_2484_);
lean_dec(v___y_2484_);
lean_dec(v___y_2482_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 4, v_r_2265_);
lean_ctor_set(v___x_2476_, 3, v_r_2471_);
lean_ctor_set(v___x_2476_, 2, v_v_2263_);
lean_ctor_set(v___x_2476_, 1, v_k_2262_);
lean_ctor_set(v___x_2476_, 0, v___x_2485_);
v___x_2487_ = v___x_2476_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2485_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2491_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2491_, 3, v_r_2471_);
lean_ctor_set(v_reuseFailAlloc_2491_, 4, v_r_2265_);
v___x_2487_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
lean_object* v___x_2489_; 
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 4, v___x_2487_);
lean_ctor_set(v___x_2464_, 3, v___y_2483_);
lean_ctor_set(v___x_2464_, 2, v_v_2469_);
lean_ctor_set(v___x_2464_, 1, v_k_2468_);
lean_ctor_set(v___x_2464_, 0, v___x_2480_);
v___x_2489_ = v___x_2464_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2480_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v_k_2468_);
lean_ctor_set(v_reuseFailAlloc_2490_, 2, v_v_2469_);
lean_ctor_set(v_reuseFailAlloc_2490_, 3, v___y_2483_);
lean_ctor_set(v_reuseFailAlloc_2490_, 4, v___x_2487_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
v___jp_2493_:
{
lean_object* v___x_2495_; lean_object* v___x_2497_; 
v___x_2495_ = lean_nat_add(v___x_2492_, v___y_2494_);
lean_dec(v___y_2494_);
lean_dec(v___x_2492_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v_l_2470_);
lean_ctor_set(v___x_2267_, 3, v_l_2452_);
lean_ctor_set(v___x_2267_, 2, v_v_2451_);
lean_ctor_set(v___x_2267_, 1, v_k_2450_);
lean_ctor_set(v___x_2267_, 0, v___x_2495_);
v___x_2497_ = v___x_2267_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2495_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v_k_2450_);
lean_ctor_set(v_reuseFailAlloc_2501_, 2, v_v_2451_);
lean_ctor_set(v_reuseFailAlloc_2501_, 3, v_l_2452_);
lean_ctor_set(v_reuseFailAlloc_2501_, 4, v_l_2470_);
v___x_2497_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
lean_object* v___x_2498_; 
v___x_2498_ = lean_nat_add(v___x_2478_, v_size_2448_);
if (lean_obj_tag(v_r_2471_) == 0)
{
lean_object* v_size_2499_; 
v_size_2499_ = lean_ctor_get(v_r_2471_, 0);
lean_inc(v_size_2499_);
v___y_2482_ = v___x_2498_;
v___y_2483_ = v___x_2497_;
v___y_2484_ = v_size_2499_;
goto v___jp_2481_;
}
else
{
lean_object* v___x_2500_; 
v___x_2500_ = lean_unsigned_to_nat(0u);
v___y_2482_ = v___x_2498_;
v___y_2483_ = v___x_2497_;
v___y_2484_ = v___x_2500_;
goto v___jp_2481_;
}
}
}
}
}
else
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2516_; 
lean_del_object(v___x_2267_);
v___x_2510_ = lean_unsigned_to_nat(1u);
v___x_2511_ = lean_nat_add(v___x_2510_, v_size_2449_);
lean_dec(v_size_2449_);
v___x_2512_ = lean_nat_add(v___x_2511_, v_size_2448_);
lean_dec(v___x_2511_);
v___x_2513_ = lean_nat_add(v___x_2510_, v_size_2448_);
v___x_2514_ = lean_nat_add(v___x_2513_, v_size_2467_);
lean_dec(v___x_2513_);
lean_inc_ref(v_r_2265_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 4, v_r_2265_);
lean_ctor_set(v___x_2464_, 3, v_r_2453_);
lean_ctor_set(v___x_2464_, 2, v_v_2263_);
lean_ctor_set(v___x_2464_, 1, v_k_2262_);
lean_ctor_set(v___x_2464_, 0, v___x_2514_);
v___x_2516_ = v___x_2464_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2514_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2529_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2529_, 3, v_r_2453_);
lean_ctor_set(v_reuseFailAlloc_2529_, 4, v_r_2265_);
v___x_2516_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
v_isSharedCheck_2523_ = !lean_is_exclusive(v_r_2265_);
if (v_isSharedCheck_2523_ == 0)
{
lean_object* v_unused_2524_; lean_object* v_unused_2525_; lean_object* v_unused_2526_; lean_object* v_unused_2527_; lean_object* v_unused_2528_; 
v_unused_2524_ = lean_ctor_get(v_r_2265_, 4);
lean_dec(v_unused_2524_);
v_unused_2525_ = lean_ctor_get(v_r_2265_, 3);
lean_dec(v_unused_2525_);
v_unused_2526_ = lean_ctor_get(v_r_2265_, 2);
lean_dec(v_unused_2526_);
v_unused_2527_ = lean_ctor_get(v_r_2265_, 1);
lean_dec(v_unused_2527_);
v_unused_2528_ = lean_ctor_get(v_r_2265_, 0);
lean_dec(v_unused_2528_);
v___x_2518_ = v_r_2265_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_dec(v_r_2265_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 4, v___x_2516_);
lean_ctor_set(v___x_2518_, 3, v_l_2452_);
lean_ctor_set(v___x_2518_, 2, v_v_2451_);
lean_ctor_set(v___x_2518_, 1, v_k_2450_);
lean_ctor_set(v___x_2518_, 0, v___x_2512_);
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_k_2450_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v_v_2451_);
lean_ctor_set(v_reuseFailAlloc_2522_, 3, v_l_2452_);
lean_ctor_set(v_reuseFailAlloc_2522_, 4, v___x_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
}
else
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
lean_dec_ref(v_l_2452_);
lean_del_object(v___x_2464_);
lean_dec(v_v_2451_);
lean_dec(v_k_2450_);
lean_dec(v_size_2449_);
lean_dec_ref(v_r_2265_);
lean_del_object(v___x_2267_);
lean_dec(v_v_2263_);
lean_dec(v_k_2262_);
v___x_2530_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__7);
v___x_2531_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2___redArg(v___x_2530_);
return v___x_2531_;
}
}
else
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
lean_del_object(v___x_2464_);
lean_dec(v_r_2453_);
lean_dec(v_v_2451_);
lean_dec(v_k_2450_);
lean_dec(v_size_2449_);
lean_dec_ref(v_r_2265_);
lean_del_object(v___x_2267_);
lean_dec(v_v_2263_);
lean_dec(v_k_2262_);
v___x_2532_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__8);
v___x_2533_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2___redArg(v___x_2532_);
return v___x_2533_;
}
}
}
}
else
{
lean_object* v_size_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2544_; 
v_size_2540_ = lean_ctor_get(v_r_2265_, 0);
v___x_2541_ = lean_unsigned_to_nat(1u);
v___x_2542_ = lean_nat_add(v___x_2541_, v_size_2540_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 3, v___x_2447_);
lean_ctor_set(v___x_2267_, 0, v___x_2542_);
v___x_2544_ = v___x_2267_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2542_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2545_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2545_, 3, v___x_2447_);
lean_ctor_set(v_reuseFailAlloc_2545_, 4, v_r_2265_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
else
{
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_l_2546_; 
v_l_2546_ = lean_ctor_get(v___x_2447_, 3);
lean_inc(v_l_2546_);
if (lean_obj_tag(v_l_2546_) == 0)
{
lean_object* v_r_2547_; 
v_r_2547_ = lean_ctor_get(v___x_2447_, 4);
lean_inc(v_r_2547_);
if (lean_obj_tag(v_r_2547_) == 0)
{
lean_object* v_size_2548_; lean_object* v_k_2549_; lean_object* v_v_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2564_; 
v_size_2548_ = lean_ctor_get(v___x_2447_, 0);
v_k_2549_ = lean_ctor_get(v___x_2447_, 1);
v_v_2550_ = lean_ctor_get(v___x_2447_, 2);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2564_ == 0)
{
lean_object* v_unused_2565_; lean_object* v_unused_2566_; 
v_unused_2565_ = lean_ctor_get(v___x_2447_, 4);
lean_dec(v_unused_2565_);
v_unused_2566_ = lean_ctor_get(v___x_2447_, 3);
lean_dec(v_unused_2566_);
v___x_2552_ = v___x_2447_;
v_isShared_2553_ = v_isSharedCheck_2564_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_v_2550_);
lean_inc(v_k_2549_);
lean_inc(v_size_2548_);
lean_dec(v___x_2447_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2564_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v_size_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2559_; 
v_size_2554_ = lean_ctor_get(v_r_2547_, 0);
v___x_2555_ = lean_unsigned_to_nat(1u);
v___x_2556_ = lean_nat_add(v___x_2555_, v_size_2548_);
lean_dec(v_size_2548_);
v___x_2557_ = lean_nat_add(v___x_2555_, v_size_2554_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 4, v_r_2265_);
lean_ctor_set(v___x_2552_, 3, v_r_2547_);
lean_ctor_set(v___x_2552_, 2, v_v_2263_);
lean_ctor_set(v___x_2552_, 1, v_k_2262_);
lean_ctor_set(v___x_2552_, 0, v___x_2557_);
v___x_2559_ = v___x_2552_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2557_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2563_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2563_, 3, v_r_2547_);
lean_ctor_set(v_reuseFailAlloc_2563_, 4, v_r_2265_);
v___x_2559_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
lean_object* v___x_2561_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v___x_2559_);
lean_ctor_set(v___x_2267_, 3, v_l_2546_);
lean_ctor_set(v___x_2267_, 2, v_v_2550_);
lean_ctor_set(v___x_2267_, 1, v_k_2549_);
lean_ctor_set(v___x_2267_, 0, v___x_2556_);
v___x_2561_ = v___x_2267_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2556_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_k_2549_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v_v_2550_);
lean_ctor_set(v_reuseFailAlloc_2562_, 3, v_l_2546_);
lean_ctor_set(v_reuseFailAlloc_2562_, 4, v___x_2559_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
else
{
lean_object* v_k_2567_; lean_object* v_v_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2580_; 
v_k_2567_ = lean_ctor_get(v___x_2447_, 1);
v_v_2568_ = lean_ctor_get(v___x_2447_, 2);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2580_ == 0)
{
lean_object* v_unused_2581_; lean_object* v_unused_2582_; lean_object* v_unused_2583_; 
v_unused_2581_ = lean_ctor_get(v___x_2447_, 4);
lean_dec(v_unused_2581_);
v_unused_2582_ = lean_ctor_get(v___x_2447_, 3);
lean_dec(v_unused_2582_);
v_unused_2583_ = lean_ctor_get(v___x_2447_, 0);
lean_dec(v_unused_2583_);
v___x_2570_ = v___x_2447_;
v_isShared_2571_ = v_isSharedCheck_2580_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_v_2568_);
lean_inc(v_k_2567_);
lean_dec(v___x_2447_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2580_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2572_ = lean_unsigned_to_nat(3u);
v___x_2573_ = lean_unsigned_to_nat(1u);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 3, v_r_2547_);
lean_ctor_set(v___x_2570_, 2, v_v_2263_);
lean_ctor_set(v___x_2570_, 1, v_k_2262_);
lean_ctor_set(v___x_2570_, 0, v___x_2573_);
v___x_2575_ = v___x_2570_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2573_);
lean_ctor_set(v_reuseFailAlloc_2579_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2579_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2579_, 3, v_r_2547_);
lean_ctor_set(v_reuseFailAlloc_2579_, 4, v_r_2547_);
v___x_2575_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
lean_object* v___x_2577_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v___x_2575_);
lean_ctor_set(v___x_2267_, 3, v_l_2546_);
lean_ctor_set(v___x_2267_, 2, v_v_2568_);
lean_ctor_set(v___x_2267_, 1, v_k_2567_);
lean_ctor_set(v___x_2267_, 0, v___x_2572_);
v___x_2577_ = v___x_2267_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2572_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v_k_2567_);
lean_ctor_set(v_reuseFailAlloc_2578_, 2, v_v_2568_);
lean_ctor_set(v_reuseFailAlloc_2578_, 3, v_l_2546_);
lean_ctor_set(v_reuseFailAlloc_2578_, 4, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
}
else
{
lean_object* v_r_2584_; 
v_r_2584_ = lean_ctor_get(v___x_2447_, 4);
lean_inc(v_r_2584_);
if (lean_obj_tag(v_r_2584_) == 0)
{
lean_object* v_k_2585_; lean_object* v_v_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2610_; 
v_k_2585_ = lean_ctor_get(v___x_2447_, 1);
v_v_2586_ = lean_ctor_get(v___x_2447_, 2);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2610_ == 0)
{
lean_object* v_unused_2611_; lean_object* v_unused_2612_; lean_object* v_unused_2613_; 
v_unused_2611_ = lean_ctor_get(v___x_2447_, 4);
lean_dec(v_unused_2611_);
v_unused_2612_ = lean_ctor_get(v___x_2447_, 3);
lean_dec(v_unused_2612_);
v_unused_2613_ = lean_ctor_get(v___x_2447_, 0);
lean_dec(v_unused_2613_);
v___x_2588_ = v___x_2447_;
v_isShared_2589_ = v_isSharedCheck_2610_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_v_2586_);
lean_inc(v_k_2585_);
lean_dec(v___x_2447_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2610_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v_k_2590_; lean_object* v_v_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2606_; 
v_k_2590_ = lean_ctor_get(v_r_2584_, 1);
v_v_2591_ = lean_ctor_get(v_r_2584_, 2);
v_isSharedCheck_2606_ = !lean_is_exclusive(v_r_2584_);
if (v_isSharedCheck_2606_ == 0)
{
lean_object* v_unused_2607_; lean_object* v_unused_2608_; lean_object* v_unused_2609_; 
v_unused_2607_ = lean_ctor_get(v_r_2584_, 4);
lean_dec(v_unused_2607_);
v_unused_2608_ = lean_ctor_get(v_r_2584_, 3);
lean_dec(v_unused_2608_);
v_unused_2609_ = lean_ctor_get(v_r_2584_, 0);
lean_dec(v_unused_2609_);
v___x_2593_ = v_r_2584_;
v_isShared_2594_ = v_isSharedCheck_2606_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_v_2591_);
lean_inc(v_k_2590_);
lean_dec(v_r_2584_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2606_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2598_; 
v___x_2595_ = lean_unsigned_to_nat(3u);
v___x_2596_ = lean_unsigned_to_nat(1u);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 4, v_l_2546_);
lean_ctor_set(v___x_2593_, 3, v_l_2546_);
lean_ctor_set(v___x_2593_, 2, v_v_2586_);
lean_ctor_set(v___x_2593_, 1, v_k_2585_);
lean_ctor_set(v___x_2593_, 0, v___x_2596_);
v___x_2598_ = v___x_2593_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2596_);
lean_ctor_set(v_reuseFailAlloc_2605_, 1, v_k_2585_);
lean_ctor_set(v_reuseFailAlloc_2605_, 2, v_v_2586_);
lean_ctor_set(v_reuseFailAlloc_2605_, 3, v_l_2546_);
lean_ctor_set(v_reuseFailAlloc_2605_, 4, v_l_2546_);
v___x_2598_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
lean_object* v___x_2600_; 
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 4, v_l_2546_);
lean_ctor_set(v___x_2588_, 2, v_v_2263_);
lean_ctor_set(v___x_2588_, 1, v_k_2262_);
lean_ctor_set(v___x_2588_, 0, v___x_2596_);
v___x_2600_ = v___x_2588_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2596_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2604_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2604_, 3, v_l_2546_);
lean_ctor_set(v_reuseFailAlloc_2604_, 4, v_l_2546_);
v___x_2600_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v___x_2602_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v___x_2600_);
lean_ctor_set(v___x_2267_, 3, v___x_2598_);
lean_ctor_set(v___x_2267_, 2, v_v_2591_);
lean_ctor_set(v___x_2267_, 1, v_k_2590_);
lean_ctor_set(v___x_2267_, 0, v___x_2595_);
v___x_2602_ = v___x_2267_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_k_2590_);
lean_ctor_set(v_reuseFailAlloc_2603_, 2, v_v_2591_);
lean_ctor_set(v_reuseFailAlloc_2603_, 3, v___x_2598_);
lean_ctor_set(v_reuseFailAlloc_2603_, 4, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
}
}
else
{
lean_object* v___x_2614_; lean_object* v___x_2616_; 
v___x_2614_ = lean_unsigned_to_nat(2u);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v_r_2584_);
lean_ctor_set(v___x_2267_, 3, v___x_2447_);
lean_ctor_set(v___x_2267_, 0, v___x_2614_);
v___x_2616_ = v___x_2267_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2614_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2617_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2617_, 3, v___x_2447_);
lean_ctor_set(v_reuseFailAlloc_2617_, 4, v_r_2584_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
else
{
lean_object* v___x_2618_; lean_object* v___x_2620_; 
v___x_2618_ = lean_unsigned_to_nat(1u);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v___x_2447_);
lean_ctor_set(v___x_2267_, 3, v___x_2447_);
lean_ctor_set(v___x_2267_, 0, v___x_2618_);
v___x_2620_ = v___x_2267_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___x_2618_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v_k_2262_);
lean_ctor_set(v_reuseFailAlloc_2621_, 2, v_v_2263_);
lean_ctor_set(v_reuseFailAlloc_2621_, 3, v___x_2447_);
lean_ctor_set(v_reuseFailAlloc_2621_, 4, v___x_2447_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
}
}
else
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = lean_unsigned_to_nat(1u);
v___x_2624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
lean_ctor_set(v___x_2624_, 1, v_k_2258_);
lean_ctor_set(v___x_2624_, 2, v_v_2259_);
lean_ctor_set(v___x_2624_, 3, v_t_2260_);
lean_ctor_set(v___x_2624_, 4, v_t_2260_);
return v___x_2624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__4(size_t v_sz_2625_, size_t v_i_2626_, lean_object* v_bs_2627_){
_start:
{
uint8_t v___x_2628_; 
v___x_2628_ = lean_usize_dec_lt(v_i_2626_, v_sz_2625_);
if (v___x_2628_ == 0)
{
return v_bs_2627_;
}
else
{
lean_object* v_v_2629_; lean_object* v___x_2630_; lean_object* v_bs_x27_2631_; lean_object* v___x_2632_; size_t v___x_2633_; size_t v___x_2634_; lean_object* v___x_2635_; 
v_v_2629_ = lean_array_uget(v_bs_2627_, v_i_2626_);
v___x_2630_ = lean_unsigned_to_nat(0u);
v_bs_x27_2631_ = lean_array_uset(v_bs_2627_, v_i_2626_, v___x_2630_);
v___x_2632_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2632_, 0, v_v_2629_);
v___x_2633_ = ((size_t)1ULL);
v___x_2634_ = lean_usize_add(v_i_2626_, v___x_2633_);
v___x_2635_ = lean_array_uset(v_bs_x27_2631_, v_i_2626_, v___x_2632_);
v_i_2626_ = v___x_2634_;
v_bs_2627_ = v___x_2635_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__4___boxed(lean_object* v_sz_2637_, lean_object* v_i_2638_, lean_object* v_bs_2639_){
_start:
{
size_t v_sz_boxed_2640_; size_t v_i_boxed_2641_; lean_object* v_res_2642_; 
v_sz_boxed_2640_ = lean_unbox_usize(v_sz_2637_);
lean_dec(v_sz_2637_);
v_i_boxed_2641_ = lean_unbox_usize(v_i_2638_);
lean_dec(v_i_2638_);
v_res_2642_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__4(v_sz_boxed_2640_, v_i_boxed_2641_, v_bs_2639_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2(lean_object* v_a_2643_){
_start:
{
size_t v_sz_2644_; size_t v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v_sz_2644_ = lean_array_size(v_a_2643_);
v___x_2645_ = ((size_t)0ULL);
v___x_2646_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__4(v_sz_2644_, v___x_2645_, v_a_2643_);
v___x_2647_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4(lean_object* v_init_2648_, lean_object* v_x_2649_){
_start:
{
if (lean_obj_tag(v_x_2649_) == 0)
{
lean_object* v_k_2650_; lean_object* v_v_2651_; lean_object* v_l_2652_; lean_object* v_r_2653_; lean_object* v___x_2654_; uint8_t v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v_k_2650_ = lean_ctor_get(v_x_2649_, 1);
lean_inc(v_k_2650_);
v_v_2651_ = lean_ctor_get(v_x_2649_, 2);
lean_inc(v_v_2651_);
v_l_2652_ = lean_ctor_get(v_x_2649_, 3);
lean_inc(v_l_2652_);
v_r_2653_ = lean_ctor_get(v_x_2649_, 4);
lean_inc(v_r_2653_);
lean_dec_ref(v_x_2649_);
v___x_2654_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4(v_init_2648_, v_l_2652_);
v___x_2655_ = 1;
v___x_2656_ = l_Lean_Name_toString(v_k_2650_, v___x_2655_);
v___x_2657_ = l_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2(v_v_2651_);
v___x_2658_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg(v___x_2656_, v___x_2657_, v___x_2654_);
v_init_2648_ = v___x_2658_;
v_x_2649_ = v_r_2653_;
goto _start;
}
else
{
return v_init_2648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1(lean_object* v_m_2660_){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2661_ = lean_box(1);
v___x_2662_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4(v___x_2661_, v_m_2660_);
v___x_2663_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_instToJsonModuleSetup_toJson_spec__0(lean_object* v_k_2664_, lean_object* v_x_2665_){
_start:
{
if (lean_obj_tag(v_x_2665_) == 0)
{
lean_object* v___x_2666_; 
lean_dec_ref(v_k_2664_);
v___x_2666_ = lean_box(0);
return v___x_2666_;
}
else
{
lean_object* v_val_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v_val_2667_ = lean_ctor_get(v_x_2665_, 0);
lean_inc(v_val_2667_);
lean_dec_ref(v_x_2665_);
v___x_2668_ = l_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0(v_val_2667_);
v___x_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2669_, 0, v_k_2664_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = lean_box(0);
v___x_2671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2669_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
return v___x_2671_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__8_spec__11(lean_object* v_init_2672_, lean_object* v_x_2673_){
_start:
{
if (lean_obj_tag(v_x_2673_) == 0)
{
lean_object* v_k_2674_; lean_object* v_v_2675_; lean_object* v_l_2676_; lean_object* v_r_2677_; lean_object* v___x_2678_; uint8_t v___x_2679_; lean_object* v___x_2680_; lean_object* v___y_2682_; 
v_k_2674_ = lean_ctor_get(v_x_2673_, 1);
lean_inc(v_k_2674_);
v_v_2675_ = lean_ctor_get(v_x_2673_, 2);
lean_inc(v_v_2675_);
v_l_2676_ = lean_ctor_get(v_x_2673_, 3);
lean_inc(v_l_2676_);
v_r_2677_ = lean_ctor_get(v_x_2673_, 4);
lean_inc(v_r_2677_);
lean_dec_ref(v_x_2673_);
v___x_2678_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__8_spec__11(v_init_2672_, v_l_2676_);
v___x_2679_ = 1;
v___x_2680_ = l_Lean_Name_toString(v_k_2674_, v___x_2679_);
switch(lean_obj_tag(v_v_2675_))
{
case 0:
{
lean_object* v_s_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
v_s_2685_ = lean_ctor_get(v_v_2675_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v_v_2675_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v_v_2675_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_s_2685_);
lean_dec(v_v_2675_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
lean_ctor_set_tag(v___x_2687_, 3);
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_s_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
v___y_2682_ = v___x_2690_;
goto v___jp_2681_;
}
}
}
case 1:
{
uint8_t v_b_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
v_b_2693_ = lean_ctor_get_uint8(v_v_2675_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v_v_2675_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v_v_2675_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_dec(v_v_2675_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2699_, 0, v_b_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
v___y_2682_ = v___x_2698_;
goto v___jp_2681_;
}
}
}
default: 
{
lean_object* v_n_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2709_; 
v_n_2701_ = lean_ctor_get(v_v_2675_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v_v_2675_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2703_ = v_v_2675_;
v_isShared_2704_ = v_isSharedCheck_2709_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_n_2701_);
lean_dec(v_v_2675_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2709_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2705_; lean_object* v___x_2707_; 
v___x_2705_ = l_Lean_JsonNumber_fromNat(v_n_2701_);
if (v_isShared_2704_ == 0)
{
lean_ctor_set(v___x_2703_, 0, v___x_2705_);
v___x_2707_ = v___x_2703_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2705_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
v___y_2682_ = v___x_2707_;
goto v___jp_2681_;
}
}
}
}
v___jp_2681_:
{
lean_object* v___x_2683_; 
v___x_2683_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg(v___x_2680_, v___y_2682_, v___x_2678_);
v_init_2672_ = v___x_2683_;
v_x_2673_ = v_r_2677_;
goto _start;
}
}
else
{
return v_init_2672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4(lean_object* v_m_2710_){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2711_ = lean_box(1);
v___x_2712_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__8_spec__11(v___x_2711_, v_m_2710_);
v___x_2713_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2712_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonModuleSetup_toJson(lean_object* v_x_2715_){
_start:
{
lean_object* v_name_2716_; lean_object* v_package_x3f_2717_; uint8_t v_isModule_2718_; lean_object* v_imports_x3f_2719_; lean_object* v_importArts_2720_; lean_object* v_dynlibs_2721_; lean_object* v_plugins_2722_; lean_object* v_options_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v_name_2716_ = lean_ctor_get(v_x_2715_, 0);
lean_inc(v_name_2716_);
v_package_x3f_2717_ = lean_ctor_get(v_x_2715_, 1);
lean_inc(v_package_x3f_2717_);
v_isModule_2718_ = lean_ctor_get_uint8(v_x_2715_, sizeof(void*)*7);
v_imports_x3f_2719_ = lean_ctor_get(v_x_2715_, 2);
lean_inc(v_imports_x3f_2719_);
v_importArts_2720_ = lean_ctor_get(v_x_2715_, 3);
lean_inc(v_importArts_2720_);
v_dynlibs_2721_ = lean_ctor_get(v_x_2715_, 4);
lean_inc_ref(v_dynlibs_2721_);
v_plugins_2722_ = lean_ctor_get(v_x_2715_, 5);
lean_inc_ref(v_plugins_2722_);
v_options_2723_ = lean_ctor_get(v_x_2715_, 6);
lean_inc(v_options_2723_);
lean_dec_ref(v_x_2715_);
v___x_2724_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__0));
v___x_2725_ = 1;
v___x_2726_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2716_, v___x_2725_);
v___x_2727_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
v___x_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2724_);
lean_ctor_set(v___x_2728_, 1, v___x_2727_);
v___x_2729_ = lean_box(0);
v___x_2730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2728_);
lean_ctor_set(v___x_2730_, 1, v___x_2729_);
v___x_2731_ = ((lean_object*)(l_Lean_instToJsonModuleSetup_toJson___closed__0));
v___x_2732_ = l_Lean_Json_opt___at___00Lean_instToJsonPlugin_toJson_spec__0(v___x_2731_, v_package_x3f_2717_);
v___x_2733_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__5));
v___x_2734_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2734_, 0, v_isModule_2718_);
v___x_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2733_);
lean_ctor_set(v___x_2735_, 1, v___x_2734_);
v___x_2736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2735_);
lean_ctor_set(v___x_2736_, 1, v___x_2729_);
v___x_2737_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__0));
v___x_2738_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleSetup_toJson_spec__0(v___x_2737_, v_imports_x3f_2719_);
v___x_2739_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__8));
v___x_2740_ = l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1(v_importArts_2720_);
v___x_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2739_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v___x_2742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2741_);
lean_ctor_set(v___x_2742_, 1, v___x_2729_);
v___x_2743_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__12));
v___x_2744_ = l_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2(v_dynlibs_2721_);
v___x_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2743_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2745_);
lean_ctor_set(v___x_2746_, 1, v___x_2729_);
v___x_2747_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__14));
v___x_2748_ = l_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3(v_plugins_2722_);
v___x_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2747_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
v___x_2750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2749_);
lean_ctor_set(v___x_2750_, 1, v___x_2729_);
v___x_2751_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__16));
v___x_2752_ = l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4(v_options_2723_);
v___x_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2751_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
lean_ctor_set(v___x_2754_, 1, v___x_2729_);
v___x_2755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2754_);
lean_ctor_set(v___x_2755_, 1, v___x_2729_);
v___x_2756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2750_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
v___x_2757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2746_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2742_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
v___x_2759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2738_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___x_2760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2736_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2732_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
v___x_2762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2730_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
v___x_2763_ = ((lean_object*)(l_Lean_instToJsonImport_toJson___closed__0));
v___x_2764_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(v___x_2762_, v___x_2763_);
v___x_2765_ = l_Lean_Json_mkObj(v___x_2764_);
lean_dec(v___x_2764_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2766_, lean_object* v_msg_2767_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2___redArg(v_msg_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1(lean_object* v_00_u03b2_2769_, lean_object* v_k_2770_, lean_object* v_v_2771_, lean_object* v_t_2772_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg(v_k_2770_, v_v_2771_, v_t_2772_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2(lean_object* v_init_2774_, lean_object* v_t_2775_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4(v_init_2774_, v_t_2775_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__8(lean_object* v_init_2777_, lean_object* v_t_2778_){
_start:
{
lean_object* v___x_2779_; 
v___x_2779_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__8_spec__11(v_init_2777_, v_t_2778_);
return v___x_2779_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__3(void){
_start:
{
lean_object* v_natZero_2786_; lean_object* v_intZero_2787_; 
v_natZero_2786_ = lean_unsigned_to_nat(0u);
v_intZero_2787_ = lean_nat_to_int(v_natZero_2786_);
return v_intZero_2787_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12(lean_object* v_init_2789_, lean_object* v_x_2790_){
_start:
{
if (lean_obj_tag(v_x_2790_) == 0)
{
lean_object* v_k_2795_; lean_object* v_v_2796_; lean_object* v_l_2797_; lean_object* v_r_2798_; lean_object* v___x_2799_; 
v_k_2795_ = lean_ctor_get(v_x_2790_, 1);
lean_inc(v_k_2795_);
v_v_2796_ = lean_ctor_get(v_x_2790_, 2);
lean_inc(v_v_2796_);
v_l_2797_ = lean_ctor_get(v_x_2790_, 3);
lean_inc(v_l_2797_);
v_r_2798_ = lean_ctor_get(v_x_2790_, 4);
lean_inc(v_r_2798_);
lean_dec_ref(v_x_2790_);
v___x_2799_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12(v_init_2789_, v_l_2797_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_dec(v_r_2798_);
lean_dec(v_v_2796_);
lean_dec(v_k_2795_);
return v___x_2799_;
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2886_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2802_ = v___x_2799_;
v_isShared_2803_ = v_isSharedCheck_2886_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2799_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2886_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v_a_2805_; lean_object* v___x_2809_; uint8_t v___x_2810_; 
v___x_2809_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__2));
v___x_2810_ = lean_string_dec_eq(v_k_2795_, v___x_2809_);
if (v___x_2810_ == 0)
{
lean_object* v_n_2811_; lean_object* v_a_2813_; uint8_t v___x_2816_; 
lean_inc(v_k_2795_);
v_n_2811_ = l_String_toName(v_k_2795_);
v___x_2816_ = l_Lean_Name_isAnonymous(v_n_2811_);
if (v___x_2816_ == 0)
{
lean_del_object(v___x_2802_);
lean_dec(v_k_2795_);
switch(lean_obj_tag(v_v_2796_))
{
case 3:
{
lean_object* v_s_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
v_s_2817_ = lean_ctor_get(v_v_2796_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v_v_2796_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v_v_2796_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_s_2817_);
lean_dec(v_v_2796_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
lean_ctor_set_tag(v___x_2819_, 0);
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_s_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
v_a_2813_ = v___x_2822_;
goto v___jp_2812_;
}
}
}
case 1:
{
uint8_t v_b_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
v_b_2825_ = lean_ctor_get_uint8(v_v_2796_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v_v_2796_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v_v_2796_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_dec(v_v_2796_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2831_, 0, v_b_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
v_a_2813_ = v___x_2830_;
goto v___jp_2812_;
}
}
}
case 2:
{
lean_object* v_n_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2847_; 
v_n_2833_ = lean_ctor_get(v_v_2796_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v_v_2796_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2835_ = v_v_2796_;
v_isShared_2836_ = v_isSharedCheck_2847_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_n_2833_);
lean_dec(v_v_2796_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2847_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v_mantissa_2837_; lean_object* v_exponent_2838_; lean_object* v_natZero_2839_; lean_object* v_intZero_2840_; uint8_t v_isNeg_2841_; 
v_mantissa_2837_ = lean_ctor_get(v_n_2833_, 0);
lean_inc(v_mantissa_2837_);
v_exponent_2838_ = lean_ctor_get(v_n_2833_, 1);
lean_inc(v_exponent_2838_);
lean_dec_ref(v_n_2833_);
v_natZero_2839_ = lean_unsigned_to_nat(0u);
v_intZero_2840_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__3, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__3);
v_isNeg_2841_ = lean_int_dec_lt(v_mantissa_2837_, v_intZero_2840_);
if (v_isNeg_2841_ == 0)
{
uint8_t v___x_2842_; 
v___x_2842_ = lean_nat_dec_eq(v_exponent_2838_, v_natZero_2839_);
lean_dec(v_exponent_2838_);
if (v___x_2842_ == 0)
{
lean_dec(v_mantissa_2837_);
lean_del_object(v___x_2835_);
lean_dec(v_n_2811_);
lean_dec(v_a_2800_);
lean_dec(v_r_2798_);
goto v___jp_2793_;
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; 
v_a_2843_ = lean_nat_abs(v_mantissa_2837_);
lean_dec(v_mantissa_2837_);
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 0, v_a_2843_);
v___x_2845_ = v___x_2835_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2843_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
v_a_2813_ = v___x_2845_;
goto v___jp_2812_;
}
}
}
else
{
lean_dec(v_exponent_2838_);
lean_dec(v_mantissa_2837_);
lean_del_object(v___x_2835_);
lean_dec(v_n_2811_);
lean_dec(v_a_2800_);
lean_dec(v_r_2798_);
goto v___jp_2793_;
}
}
}
default: 
{
lean_dec(v_n_2811_);
lean_dec(v_a_2800_);
lean_dec(v_r_2798_);
lean_dec(v_v_2796_);
goto v___jp_2793_;
}
}
}
else
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2853_; 
lean_dec(v_n_2811_);
lean_dec(v_a_2800_);
lean_dec(v_r_2798_);
lean_dec(v_v_2796_);
v___x_2848_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__4));
v___x_2849_ = lean_string_append(v___x_2848_, v_k_2795_);
lean_dec(v_k_2795_);
v___x_2850_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_2851_ = lean_string_append(v___x_2849_, v___x_2850_);
if (v_isShared_2803_ == 0)
{
lean_ctor_set_tag(v___x_2802_, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2851_);
v___x_2853_ = v___x_2802_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2851_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
v___jp_2812_:
{
lean_object* v___x_2814_; 
v___x_2814_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_2811_, v_a_2813_, v_a_2800_);
v_init_2789_ = v___x_2814_;
v_x_2790_ = v_r_2798_;
goto _start;
}
}
else
{
lean_del_object(v___x_2802_);
lean_dec(v_k_2795_);
switch(lean_obj_tag(v_v_2796_))
{
case 3:
{
lean_object* v_s_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
v_s_2855_ = lean_ctor_get(v_v_2796_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v_v_2796_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v_v_2796_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_s_2855_);
lean_dec(v_v_2796_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
lean_ctor_set_tag(v___x_2857_, 0);
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_s_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
v_a_2805_ = v___x_2860_;
goto v___jp_2804_;
}
}
}
case 1:
{
uint8_t v_b_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
v_b_2863_ = lean_ctor_get_uint8(v_v_2796_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v_v_2796_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v_v_2796_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_dec(v_v_2796_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2869_, 0, v_b_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
v_a_2805_ = v___x_2868_;
goto v___jp_2804_;
}
}
}
case 2:
{
lean_object* v_n_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2885_; 
v_n_2871_ = lean_ctor_get(v_v_2796_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v_v_2796_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2873_ = v_v_2796_;
v_isShared_2874_ = v_isSharedCheck_2885_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_n_2871_);
lean_dec(v_v_2796_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2885_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v_mantissa_2875_; lean_object* v_exponent_2876_; lean_object* v_natZero_2877_; lean_object* v_intZero_2878_; uint8_t v_isNeg_2879_; 
v_mantissa_2875_ = lean_ctor_get(v_n_2871_, 0);
lean_inc(v_mantissa_2875_);
v_exponent_2876_ = lean_ctor_get(v_n_2871_, 1);
lean_inc(v_exponent_2876_);
lean_dec_ref(v_n_2871_);
v_natZero_2877_ = lean_unsigned_to_nat(0u);
v_intZero_2878_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__3, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__3);
v_isNeg_2879_ = lean_int_dec_lt(v_mantissa_2875_, v_intZero_2878_);
if (v_isNeg_2879_ == 0)
{
uint8_t v___x_2880_; 
v___x_2880_ = lean_nat_dec_eq(v_exponent_2876_, v_natZero_2877_);
lean_dec(v_exponent_2876_);
if (v___x_2880_ == 0)
{
lean_dec(v_mantissa_2875_);
lean_del_object(v___x_2873_);
lean_dec(v_a_2800_);
lean_dec(v_r_2798_);
goto v___jp_2791_;
}
else
{
lean_object* v_a_2881_; lean_object* v___x_2883_; 
v_a_2881_ = lean_nat_abs(v_mantissa_2875_);
lean_dec(v_mantissa_2875_);
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 0, v_a_2881_);
v___x_2883_ = v___x_2873_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2881_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
v_a_2805_ = v___x_2883_;
goto v___jp_2804_;
}
}
}
else
{
lean_dec(v_exponent_2876_);
lean_dec(v_mantissa_2875_);
lean_del_object(v___x_2873_);
lean_dec(v_a_2800_);
lean_dec(v_r_2798_);
goto v___jp_2791_;
}
}
}
default: 
{
lean_dec(v_a_2800_);
lean_dec(v_r_2798_);
lean_dec(v_v_2796_);
goto v___jp_2791_;
}
}
}
v___jp_2804_:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = lean_box(0);
v___x_2807_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2806_, v_a_2805_, v_a_2800_);
v_init_2789_ = v___x_2807_;
v_x_2790_ = v_r_2798_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_2887_; 
v___x_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2887_, 0, v_init_2789_);
return v___x_2887_;
}
v___jp_2791_:
{
lean_object* v___x_2792_; 
v___x_2792_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__1));
return v___x_2792_;
}
v___jp_2793_:
{
lean_object* v___x_2794_; 
v___x_2794_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__1));
return v___x_2794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8(lean_object* v_x_2889_){
_start:
{
if (lean_obj_tag(v_x_2889_) == 5)
{
lean_object* v_kvPairs_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v_kvPairs_2890_ = lean_ctor_get(v_x_2889_, 0);
lean_inc(v_kvPairs_2890_);
lean_dec_ref(v_x_2889_);
v___x_2891_ = lean_box(1);
v___x_2892_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12(v___x_2891_, v_kvPairs_2890_);
return v___x_2892_;
}
else
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2893_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8___closed__0));
v___x_2894_ = lean_unsigned_to_nat(80u);
v___x_2895_ = l_Lean_Json_pretty(v_x_2889_, v___x_2894_);
v___x_2896_ = lean_string_append(v___x_2893_, v___x_2895_);
lean_dec_ref(v___x_2895_);
v___x_2897_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_2898_ = lean_string_append(v___x_2896_, v___x_2897_);
v___x_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
return v___x_2899_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4(lean_object* v_j_2900_, lean_object* v_k_2901_){
_start:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = l_Lean_Json_getObjValD(v_j_2900_, v_k_2901_);
v___x_2903_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8(v___x_2902_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2903_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2903_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
v_a_2912_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2903_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2903_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4___boxed(lean_object* v_j_2920_, lean_object* v_k_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4(v_j_2920_, v_k_2921_);
lean_dec_ref(v_k_2921_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__9(size_t v_sz_2923_, size_t v_i_2924_, lean_object* v_bs_2925_){
_start:
{
uint8_t v___x_2926_; 
v___x_2926_ = lean_usize_dec_lt(v_i_2924_, v_sz_2923_);
if (v___x_2926_ == 0)
{
lean_object* v___x_2927_; 
v___x_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2927_, 0, v_bs_2925_);
return v___x_2927_;
}
else
{
lean_object* v_v_2928_; lean_object* v___x_2929_; 
v_v_2928_ = lean_array_uget_borrowed(v_bs_2925_, v_i_2924_);
lean_inc(v_v_2928_);
v___x_2929_ = l_Lean_Plugin_fromJson_x3f(v_v_2928_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_dec_ref(v_bs_2925_);
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2929_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2929_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
else
{
lean_object* v_a_2938_; lean_object* v___x_2939_; lean_object* v_bs_x27_2940_; size_t v___x_2941_; size_t v___x_2942_; lean_object* v___x_2943_; 
v_a_2938_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_a_2938_);
lean_dec_ref(v___x_2929_);
v___x_2939_ = lean_unsigned_to_nat(0u);
v_bs_x27_2940_ = lean_array_uset(v_bs_2925_, v_i_2924_, v___x_2939_);
v___x_2941_ = ((size_t)1ULL);
v___x_2942_ = lean_usize_add(v_i_2924_, v___x_2941_);
v___x_2943_ = lean_array_uset(v_bs_x27_2940_, v_i_2924_, v_a_2938_);
v_i_2924_ = v___x_2942_;
v_bs_2925_ = v___x_2943_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__9___boxed(lean_object* v_sz_2945_, lean_object* v_i_2946_, lean_object* v_bs_2947_){
_start:
{
size_t v_sz_boxed_2948_; size_t v_i_boxed_2949_; lean_object* v_res_2950_; 
v_sz_boxed_2948_ = lean_unbox_usize(v_sz_2945_);
lean_dec(v_sz_2945_);
v_i_boxed_2949_ = lean_unbox_usize(v_i_2946_);
lean_dec(v_i_2946_);
v_res_2950_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__9(v_sz_boxed_2948_, v_i_boxed_2949_, v_bs_2947_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6(lean_object* v_x_2951_){
_start:
{
if (lean_obj_tag(v_x_2951_) == 4)
{
lean_object* v_elems_2952_; size_t v_sz_2953_; size_t v___x_2954_; lean_object* v___x_2955_; 
v_elems_2952_ = lean_ctor_get(v_x_2951_, 0);
lean_inc_ref(v_elems_2952_);
lean_dec_ref(v_x_2951_);
v_sz_2953_ = lean_array_size(v_elems_2952_);
v___x_2954_ = ((size_t)0ULL);
v___x_2955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__9(v_sz_2953_, v___x_2954_, v_elems_2952_);
return v___x_2955_;
}
else
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2956_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0));
v___x_2957_ = lean_unsigned_to_nat(80u);
v___x_2958_ = l_Lean_Json_pretty(v_x_2951_, v___x_2957_);
v___x_2959_ = lean_string_append(v___x_2956_, v___x_2958_);
lean_dec_ref(v___x_2958_);
v___x_2960_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_2961_ = lean_string_append(v___x_2959_, v___x_2960_);
v___x_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
return v___x_2962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3(lean_object* v_j_2963_, lean_object* v_k_2964_){
_start:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2965_ = l_Lean_Json_getObjValD(v_j_2963_, v_k_2964_);
v___x_2966_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6(v___x_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3___boxed(lean_object* v_j_2967_, lean_object* v_k_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3(v_j_2967_, v_k_2968_);
lean_dec_ref(v_k_2968_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0(lean_object* v_x_2972_){
_start:
{
if (lean_obj_tag(v_x_2972_) == 0)
{
lean_object* v___x_2973_; 
v___x_2973_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0___closed__0));
return v___x_2973_;
}
else
{
lean_object* v___x_2974_; 
v___x_2974_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0(v_x_2972_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2974_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2974_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2991_; 
v_a_2983_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2985_ = v___x_2974_;
v_isShared_2986_ = v_isSharedCheck_2991_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2974_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2991_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2987_; lean_object* v___x_2989_; 
v___x_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2987_, 0, v_a_2983_);
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 0, v___x_2987_);
v___x_2989_ = v___x_2985_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2987_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0(lean_object* v_j_2992_, lean_object* v_k_2993_){
_start:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = l_Lean_Json_getObjValD(v_j_2992_, v_k_2993_);
v___x_2995_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0(v___x_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0___boxed(lean_object* v_j_2996_, lean_object* v_k_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0(v_j_2996_, v_k_2997_);
lean_dec_ref(v_k_2997_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__6(size_t v_sz_2999_, size_t v_i_3000_, lean_object* v_bs_3001_){
_start:
{
uint8_t v___x_3002_; 
v___x_3002_ = lean_usize_dec_lt(v_i_3000_, v_sz_2999_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; 
v___x_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3003_, 0, v_bs_3001_);
return v___x_3003_;
}
else
{
lean_object* v_v_3004_; lean_object* v___x_3005_; 
v_v_3004_ = lean_array_uget_borrowed(v_bs_3001_, v_i_3000_);
lean_inc(v_v_3004_);
v___x_3005_ = l_Lean_Json_getStr_x3f(v_v_3004_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_dec_ref(v_bs_3001_);
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_3005_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_3005_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3015_; lean_object* v_bs_x27_3016_; size_t v___x_3017_; size_t v___x_3018_; lean_object* v___x_3019_; 
v_a_3014_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3014_);
lean_dec_ref(v___x_3005_);
v___x_3015_ = lean_unsigned_to_nat(0u);
v_bs_x27_3016_ = lean_array_uset(v_bs_3001_, v_i_3000_, v___x_3015_);
v___x_3017_ = ((size_t)1ULL);
v___x_3018_ = lean_usize_add(v_i_3000_, v___x_3017_);
v___x_3019_ = lean_array_uset(v_bs_x27_3016_, v_i_3000_, v_a_3014_);
v_i_3000_ = v___x_3018_;
v_bs_3001_ = v___x_3019_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__6___boxed(lean_object* v_sz_3021_, lean_object* v_i_3022_, lean_object* v_bs_3023_){
_start:
{
size_t v_sz_boxed_3024_; size_t v_i_boxed_3025_; lean_object* v_res_3026_; 
v_sz_boxed_3024_ = lean_unbox_usize(v_sz_3021_);
lean_dec(v_sz_3021_);
v_i_boxed_3025_ = lean_unbox_usize(v_i_3022_);
lean_dec(v_i_3022_);
v_res_3026_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__6(v_sz_boxed_3024_, v_i_boxed_3025_, v_bs_3023_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4(lean_object* v_x_3027_){
_start:
{
if (lean_obj_tag(v_x_3027_) == 4)
{
lean_object* v_elems_3028_; size_t v_sz_3029_; size_t v___x_3030_; lean_object* v___x_3031_; 
v_elems_3028_ = lean_ctor_get(v_x_3027_, 0);
lean_inc_ref(v_elems_3028_);
lean_dec_ref(v_x_3027_);
v_sz_3029_ = lean_array_size(v_elems_3028_);
v___x_3030_ = ((size_t)0ULL);
v___x_3031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__6(v_sz_3029_, v___x_3030_, v_elems_3028_);
return v___x_3031_;
}
else
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3032_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0));
v___x_3033_ = lean_unsigned_to_nat(80u);
v___x_3034_ = l_Lean_Json_pretty(v_x_3027_, v___x_3033_);
v___x_3035_ = lean_string_append(v___x_3032_, v___x_3034_);
lean_dec_ref(v___x_3034_);
v___x_3036_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_3037_ = lean_string_append(v___x_3035_, v___x_3036_);
v___x_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
return v___x_3038_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3(lean_object* v_init_3039_, lean_object* v_x_3040_){
_start:
{
if (lean_obj_tag(v_x_3040_) == 0)
{
lean_object* v_k_3041_; lean_object* v_v_3042_; lean_object* v_l_3043_; lean_object* v_r_3044_; lean_object* v___x_3045_; 
v_k_3041_ = lean_ctor_get(v_x_3040_, 1);
lean_inc(v_k_3041_);
v_v_3042_ = lean_ctor_get(v_x_3040_, 2);
lean_inc(v_v_3042_);
v_l_3043_ = lean_ctor_get(v_x_3040_, 3);
lean_inc(v_l_3043_);
v_r_3044_ = lean_ctor_get(v_x_3040_, 4);
lean_inc(v_r_3044_);
lean_dec_ref(v_x_3040_);
v___x_3045_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3(v_init_3039_, v_l_3043_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_dec(v_r_3044_);
lean_dec(v_v_3042_);
lean_dec(v_k_3041_);
return v___x_3045_;
}
else
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3086_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3048_ = v___x_3045_;
v_isShared_3049_ = v_isSharedCheck_3086_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_3045_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3086_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3050_; uint8_t v___x_3051_; 
v___x_3050_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__2));
v___x_3051_ = lean_string_dec_eq(v_k_3041_, v___x_3050_);
if (v___x_3051_ == 0)
{
lean_object* v_n_3052_; uint8_t v___x_3053_; 
lean_inc(v_k_3041_);
v_n_3052_ = l_String_toName(v_k_3041_);
v___x_3053_ = l_Lean_Name_isAnonymous(v_n_3052_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; 
lean_del_object(v___x_3048_);
lean_dec(v_k_3041_);
v___x_3054_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4(v_v_3042_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_dec(v_n_3052_);
lean_dec(v_a_3046_);
lean_dec(v_r_3044_);
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_3054_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3054_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3064_; 
v_a_3063_ = lean_ctor_get(v___x_3054_, 0);
lean_inc(v_a_3063_);
lean_dec_ref(v___x_3054_);
v___x_3064_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_3052_, v_a_3063_, v_a_3046_);
v_init_3039_ = v___x_3064_;
v_x_3040_ = v_r_3044_;
goto _start;
}
}
else
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3071_; 
lean_dec(v_n_3052_);
lean_dec(v_a_3046_);
lean_dec(v_r_3044_);
lean_dec(v_v_3042_);
v___x_3066_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__4));
v___x_3067_ = lean_string_append(v___x_3066_, v_k_3041_);
lean_dec(v_k_3041_);
v___x_3068_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_3069_ = lean_string_append(v___x_3067_, v___x_3068_);
if (v_isShared_3049_ == 0)
{
lean_ctor_set_tag(v___x_3048_, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3069_);
v___x_3071_ = v___x_3048_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3069_);
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
lean_object* v___x_3073_; 
lean_del_object(v___x_3048_);
lean_dec(v_k_3041_);
v___x_3073_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4(v_v_3042_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec(v_a_3046_);
lean_dec(v_r_3044_);
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_3073_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3073_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v_a_3082_ = lean_ctor_get(v___x_3073_, 0);
lean_inc(v_a_3082_);
lean_dec_ref(v___x_3073_);
v___x_3083_ = lean_box(0);
v___x_3084_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_3083_, v_a_3082_, v_a_3046_);
v_init_3039_ = v___x_3084_;
v_x_3040_ = v_r_3044_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_3087_; 
v___x_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3087_, 0, v_init_3039_);
return v___x_3087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2(lean_object* v_x_3088_){
_start:
{
if (lean_obj_tag(v_x_3088_) == 5)
{
lean_object* v_kvPairs_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v_kvPairs_3089_ = lean_ctor_get(v_x_3088_, 0);
lean_inc(v_kvPairs_3089_);
lean_dec_ref(v_x_3088_);
v___x_3090_ = lean_box(1);
v___x_3091_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3(v___x_3090_, v_kvPairs_3089_);
return v___x_3091_;
}
else
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3092_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8___closed__0));
v___x_3093_ = lean_unsigned_to_nat(80u);
v___x_3094_ = l_Lean_Json_pretty(v_x_3088_, v___x_3093_);
v___x_3095_ = lean_string_append(v___x_3092_, v___x_3094_);
lean_dec_ref(v___x_3094_);
v___x_3096_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1));
v___x_3097_ = lean_string_append(v___x_3095_, v___x_3096_);
v___x_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3097_);
return v___x_3098_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1(lean_object* v_j_3099_, lean_object* v_k_3100_){
_start:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3101_ = l_Lean_Json_getObjValD(v_j_3099_, v_k_3100_);
v___x_3102_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2(v___x_3101_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1___boxed(lean_object* v_j_3103_, lean_object* v_k_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1(v_j_3103_, v_k_3104_);
lean_dec_ref(v_k_3104_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2(lean_object* v_j_3106_, lean_object* v_k_3107_){
_start:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3108_ = l_Lean_Json_getObjValD(v_j_3106_, v_k_3107_);
v___x_3109_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4(v___x_3108_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2___boxed(lean_object* v_j_3110_, lean_object* v_k_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2(v_j_3110_, v_k_3111_);
lean_dec_ref(v_k_3111_);
return v_res_3112_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3117_ = 1;
v___x_3118_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__1));
v___x_3119_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3118_, v___x_3117_);
return v___x_3119_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3120_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__4));
v___x_3121_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__2, &l_Lean_instFromJsonModuleSetup_fromJson___closed__2_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__2);
v___x_3122_ = lean_string_append(v___x_3121_, v___x_3120_);
return v___x_3122_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__5(void){
_start:
{
uint8_t v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3125_ = 1;
v___x_3126_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__4));
v___x_3127_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3126_, v___x_3125_);
return v___x_3127_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__6(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3128_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__5, &l_Lean_instFromJsonModuleSetup_fromJson___closed__5_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__5);
v___x_3129_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3130_ = lean_string_append(v___x_3129_, v___x_3128_);
return v___x_3130_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3131_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3132_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__6, &l_Lean_instFromJsonModuleSetup_fromJson___closed__6_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__6);
v___x_3133_ = lean_string_append(v___x_3132_, v___x_3131_);
return v___x_3133_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__9(void){
_start:
{
uint8_t v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3136_ = 1;
v___x_3137_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__8));
v___x_3138_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3137_, v___x_3136_);
return v___x_3138_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3139_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__9, &l_Lean_instFromJsonModuleSetup_fromJson___closed__9_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__9);
v___x_3140_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3141_ = lean_string_append(v___x_3140_, v___x_3139_);
return v___x_3141_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__11(void){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3142_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3143_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__10, &l_Lean_instFromJsonModuleSetup_fromJson___closed__10_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__10);
v___x_3144_ = lean_string_append(v___x_3143_, v___x_3142_);
return v___x_3144_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3145_ = lean_obj_once(&l_Lean_instFromJsonModuleHeader_fromJson___closed__9, &l_Lean_instFromJsonModuleHeader_fromJson___closed__9_once, _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__9);
v___x_3146_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3147_ = lean_string_append(v___x_3146_, v___x_3145_);
return v___x_3147_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__13(void){
_start:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3148_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3149_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__12, &l_Lean_instFromJsonModuleSetup_fromJson___closed__12_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__12);
v___x_3150_ = lean_string_append(v___x_3149_, v___x_3148_);
return v___x_3150_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__15(void){
_start:
{
uint8_t v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3153_ = 1;
v___x_3154_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__14));
v___x_3155_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3154_, v___x_3153_);
return v___x_3155_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__16(void){
_start:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3156_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__15, &l_Lean_instFromJsonModuleSetup_fromJson___closed__15_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__15);
v___x_3157_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3158_ = lean_string_append(v___x_3157_, v___x_3156_);
return v___x_3158_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__17(void){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3159_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3160_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__16, &l_Lean_instFromJsonModuleSetup_fromJson___closed__16_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__16);
v___x_3161_ = lean_string_append(v___x_3160_, v___x_3159_);
return v___x_3161_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__19(void){
_start:
{
uint8_t v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3164_ = 1;
v___x_3165_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__18));
v___x_3166_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3165_, v___x_3164_);
return v___x_3166_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__20(void){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3167_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__19, &l_Lean_instFromJsonModuleSetup_fromJson___closed__19_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__19);
v___x_3168_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3169_ = lean_string_append(v___x_3168_, v___x_3167_);
return v___x_3169_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__21(void){
_start:
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3170_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3171_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__20, &l_Lean_instFromJsonModuleSetup_fromJson___closed__20_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__20);
v___x_3172_ = lean_string_append(v___x_3171_, v___x_3170_);
return v___x_3172_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__23(void){
_start:
{
uint8_t v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3175_ = 1;
v___x_3176_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__22));
v___x_3177_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3176_, v___x_3175_);
return v___x_3177_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__24(void){
_start:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3178_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__23, &l_Lean_instFromJsonModuleSetup_fromJson___closed__23_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__23);
v___x_3179_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3180_ = lean_string_append(v___x_3179_, v___x_3178_);
return v___x_3180_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__25(void){
_start:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3181_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3182_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__24, &l_Lean_instFromJsonModuleSetup_fromJson___closed__24_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__24);
v___x_3183_ = lean_string_append(v___x_3182_, v___x_3181_);
return v___x_3183_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__27(void){
_start:
{
uint8_t v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3186_ = 1;
v___x_3187_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__26));
v___x_3188_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3187_, v___x_3186_);
return v___x_3188_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__28(void){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3189_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__27, &l_Lean_instFromJsonModuleSetup_fromJson___closed__27_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__27);
v___x_3190_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3191_ = lean_string_append(v___x_3190_, v___x_3189_);
return v___x_3191_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__29(void){
_start:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3192_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3193_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__28, &l_Lean_instFromJsonModuleSetup_fromJson___closed__28_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__28);
v___x_3194_ = lean_string_append(v___x_3193_, v___x_3192_);
return v___x_3194_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__31(void){
_start:
{
uint8_t v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3197_ = 1;
v___x_3198_ = ((lean_object*)(l_Lean_instFromJsonModuleSetup_fromJson___closed__30));
v___x_3199_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3198_, v___x_3197_);
return v___x_3199_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__32(void){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3200_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__31, &l_Lean_instFromJsonModuleSetup_fromJson___closed__31_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__31);
v___x_3201_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__3, &l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3);
v___x_3202_ = lean_string_append(v___x_3201_, v___x_3200_);
return v___x_3202_;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__33(void){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3203_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3204_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__32, &l_Lean_instFromJsonModuleSetup_fromJson___closed__32_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__32);
v___x_3205_ = lean_string_append(v___x_3204_, v___x_3203_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonModuleSetup_fromJson(lean_object* v_json_3206_){
_start:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3207_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__0));
lean_inc(v_json_3206_);
v___x_3208_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__0(v_json_3206_, v___x_3207_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3218_; 
lean_dec(v_json_3206_);
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3211_ = v___x_3208_;
v_isShared_3212_ = v_isSharedCheck_3218_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3208_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3218_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3216_; 
v___x_3213_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__7, &l_Lean_instFromJsonModuleSetup_fromJson___closed__7_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__7);
v___x_3214_ = lean_string_append(v___x_3213_, v_a_3209_);
lean_dec(v_a_3209_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 0, v___x_3214_);
v___x_3216_ = v___x_3211_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3214_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
else
{
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_dec(v_json_3206_);
v_a_3219_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3208_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3208_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
lean_ctor_set_tag(v___x_3221_, 0);
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v_a_3227_ = lean_ctor_get(v___x_3208_, 0);
lean_inc(v_a_3227_);
lean_dec_ref(v___x_3208_);
v___x_3228_ = ((lean_object*)(l_Lean_instToJsonModuleSetup_toJson___closed__0));
lean_inc(v_json_3206_);
v___x_3229_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1(v_json_3206_, v___x_3228_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3239_; 
lean_dec(v_a_3227_);
lean_dec(v_json_3206_);
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3232_ = v___x_3229_;
v_isShared_3233_ = v_isSharedCheck_3239_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3229_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3239_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3237_; 
v___x_3234_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__11, &l_Lean_instFromJsonModuleSetup_fromJson___closed__11_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__11);
v___x_3235_ = lean_string_append(v___x_3234_, v_a_3230_);
lean_dec(v_a_3230_);
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 0, v___x_3235_);
v___x_3237_ = v___x_3232_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3235_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
else
{
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec(v_a_3227_);
lean_dec(v_json_3206_);
v_a_3240_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3229_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3229_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
lean_ctor_set_tag(v___x_3242_, 0);
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v_a_3248_ = lean_ctor_get(v___x_3229_, 0);
lean_inc(v_a_3248_);
lean_dec_ref(v___x_3229_);
v___x_3249_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__5));
lean_inc(v_json_3206_);
v___x_3250_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(v_json_3206_, v___x_3249_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3260_; 
lean_dec(v_a_3248_);
lean_dec(v_a_3227_);
lean_dec(v_json_3206_);
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3253_ = v___x_3250_;
v_isShared_3254_ = v_isSharedCheck_3260_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3250_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3260_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3258_; 
v___x_3255_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__13, &l_Lean_instFromJsonModuleSetup_fromJson___closed__13_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__13);
v___x_3256_ = lean_string_append(v___x_3255_, v_a_3251_);
lean_dec(v_a_3251_);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 0, v___x_3256_);
v___x_3258_ = v___x_3253_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v___x_3256_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
else
{
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
lean_dec(v_a_3248_);
lean_dec(v_a_3227_);
lean_dec(v_json_3206_);
v_a_3261_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v___x_3250_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3250_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
lean_ctor_set_tag(v___x_3263_, 0);
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3261_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
else
{
lean_object* v_a_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v_a_3269_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3269_);
lean_dec_ref(v___x_3250_);
v___x_3270_ = ((lean_object*)(l_Lean_instReprModuleHeader_repr___redArg___closed__0));
lean_inc(v_json_3206_);
v___x_3271_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0(v_json_3206_, v___x_3270_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3281_; 
lean_dec(v_a_3269_);
lean_dec(v_a_3248_);
lean_dec(v_a_3227_);
lean_dec(v_json_3206_);
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3274_ = v___x_3271_;
v_isShared_3275_ = v_isSharedCheck_3281_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3271_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3281_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3279_; 
v___x_3276_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__17, &l_Lean_instFromJsonModuleSetup_fromJson___closed__17_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__17);
v___x_3277_ = lean_string_append(v___x_3276_, v_a_3272_);
lean_dec(v_a_3272_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v___x_3277_);
v___x_3279_ = v___x_3274_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v___x_3277_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
else
{
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3289_; 
lean_dec(v_a_3269_);
lean_dec(v_a_3248_);
lean_dec(v_a_3227_);
lean_dec(v_json_3206_);
v_a_3282_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3284_ = v___x_3271_;
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3271_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3287_; 
if (v_isShared_3285_ == 0)
{
lean_ctor_set_tag(v___x_3284_, 0);
v___x_3287_ = v___x_3284_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_a_3282_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
else
{
lean_object* v_a_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v_a_3290_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3290_);
lean_dec_ref(v___x_3271_);
v___x_3291_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__8));
lean_inc(v_json_3206_);
v___x_3292_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1(v_json_3206_, v___x_3291_);
if (lean_obj_tag(v___x_3292_) == 0)
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3302_; 
lean_dec(v_a_3290_);
lean_dec(v_a_3269_);
lean_dec(v_a_3248_);
lean_dec(v_a_3227_);
lean_dec(v_json_3206_);
v_a_3293_ = lean_ctor_get(v___x_3292_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3295_ = v___x_3292_;
v_isShared_3296_ = v_isSharedCheck_3302_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3292_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3302_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3300_; 
v___x_3297_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__21, &l_Lean_instFromJsonModuleSetup_fromJson___closed__21_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__21);
v___x_3298_ = lean_string_append(v___x_3297_, v_a_3293_);
lean_dec(v_a_3293_);
if (v_isShared_3296_ == 0)
{
lean_ctor_set(v___x_3295_, 0, v___x_3298_);
v___x_3300_ = v___x_3295_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3298_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
else
{
if (lean_obj_tag(v___x_3292_) == 0)
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
lean_dec(v_a_3290_);
lean_dec(v_a_3269_);
lean_dec(v_a_3248_);
lean_dec(v_a_3227_);
lean_dec(v_json_3206_);
v_a_3303_ = lean_ctor_get(v___x_3292_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3292_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3292_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
lean_ctor_set_tag(v___x_3305_, 0);
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
else
{
lean_object* v_a_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v_a_3311_ = lean_ctor_get(v___x_3292_, 0);
lean_inc(v_a_3311_);
lean_dec_ref(v___x_3292_);
v___x_3312_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__12));
lean_inc(v_json_3206_);
v___x_3313_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2(v_json_3206_, v___x_3312_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3323_; 
lean_dec(v_a_3311_);
lean_dec(v_a_3290_);
lean_dec(v_a_3269_);
lean_dec(v_a_3248_);
lean_dec(v_a_3227_);
lean_dec(v_json_3206_);
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3316_ = v___x_3313_;
v_isShared_3317_ = v_isSharedCheck_3323_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3313_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3323_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3321_; 
v___x_3318_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__25, &l_Lean_instFromJsonModuleSetup_fromJson___closed__25_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__25);
v___x_3319_ = lean_string_append(v___x_3318_, v_a_3314_);
lean_dec(v_a_3314_);
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 0, v___x_3319_);
v___x_3321_ = v___x_3316_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3319_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
else
{
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3331_; 
lean_dec(v_a_3311_);
lean_dec(v_a_3290_);
lean_dec(v_a_3269_);
lean_dec(v_a_3248_);
lean_dec(v_a_3227_);
lean_dec(v_json_3206_);
v_a_3324_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3326_ = v___x_3313_;
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3313_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3329_; 
if (v_isShared_3327_ == 0)
{
lean_ctor_set_tag(v___x_3326_, 0);
v___x_3329_ = v___x_3326_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
else
{
lean_object* v_a_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v_a_3332_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_a_3332_);
lean_dec_ref(v___x_3313_);
v___x_3333_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__14));
lean_inc(v_json_3206_);
v___x_3334_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3(v_json_3206_, v___x_3333_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3344_; 
lean_dec(v_a_3332_);
lean_dec(v_a_3311_);
lean_dec(v_a_3290_);
lean_dec(v_a_3269_);
lean_dec(v_a_3248_);
lean_dec(v_a_3227_);
lean_dec(v_json_3206_);
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3337_ = v___x_3334_;
v_isShared_3338_ = v_isSharedCheck_3344_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3334_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3344_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3342_; 
v___x_3339_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__29, &l_Lean_instFromJsonModuleSetup_fromJson___closed__29_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__29);
v___x_3340_ = lean_string_append(v___x_3339_, v_a_3335_);
lean_dec(v_a_3335_);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 0, v___x_3340_);
v___x_3342_ = v___x_3337_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3340_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
else
{
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec(v_a_3332_);
lean_dec(v_a_3311_);
lean_dec(v_a_3290_);
lean_dec(v_a_3269_);
lean_dec(v_a_3248_);
lean_dec(v_a_3227_);
lean_dec(v_json_3206_);
v_a_3345_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3334_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3334_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
lean_ctor_set_tag(v___x_3347_, 0);
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
else
{
lean_object* v_a_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v_a_3353_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3353_);
lean_dec_ref(v___x_3334_);
v___x_3354_ = ((lean_object*)(l_Lean_instReprModuleSetup_repr___redArg___closed__16));
v___x_3355_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4(v_json_3206_, v___x_3354_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3365_; 
lean_dec(v_a_3353_);
lean_dec(v_a_3332_);
lean_dec(v_a_3311_);
lean_dec(v_a_3290_);
lean_dec(v_a_3269_);
lean_dec(v_a_3248_);
lean_dec(v_a_3227_);
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3358_ = v___x_3355_;
v_isShared_3359_ = v_isSharedCheck_3365_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3355_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3365_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3363_; 
v___x_3360_ = lean_obj_once(&l_Lean_instFromJsonModuleSetup_fromJson___closed__33, &l_Lean_instFromJsonModuleSetup_fromJson___closed__33_once, _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__33);
v___x_3361_ = lean_string_append(v___x_3360_, v_a_3356_);
lean_dec(v_a_3356_);
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 0, v___x_3361_);
v___x_3363_ = v___x_3358_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3361_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
else
{
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
lean_dec(v_a_3353_);
lean_dec(v_a_3332_);
lean_dec(v_a_3311_);
lean_dec(v_a_3290_);
lean_dec(v_a_3269_);
lean_dec(v_a_3248_);
lean_dec(v_a_3227_);
v_a_3366_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v___x_3355_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3355_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set_tag(v___x_3368_, 0);
v___x_3371_ = v___x_3368_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_a_3366_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
else
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3383_; 
v_a_3374_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3376_ = v___x_3355_;
v_isShared_3377_ = v_isSharedCheck_3383_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3355_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3383_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3378_; uint8_t v___x_3379_; lean_object* v___x_3381_; 
v___x_3378_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3378_, 0, v_a_3227_);
lean_ctor_set(v___x_3378_, 1, v_a_3248_);
lean_ctor_set(v___x_3378_, 2, v_a_3290_);
lean_ctor_set(v___x_3378_, 3, v_a_3311_);
lean_ctor_set(v___x_3378_, 4, v_a_3332_);
lean_ctor_set(v___x_3378_, 5, v_a_3353_);
lean_ctor_set(v___x_3378_, 6, v_a_3374_);
v___x_3379_ = lean_unbox(v_a_3269_);
lean_dec(v_a_3269_);
lean_ctor_set_uint8(v___x_3378_, sizeof(void*)*7, v___x_3379_);
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 0, v___x_3378_);
v___x_3381_ = v___x_3376_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3378_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
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
LEAN_EXPORT lean_object* l_Lean_ModuleSetup_load(lean_object* v_path_3387_){
_start:
{
lean_object* v___x_3389_; 
v___x_3389_ = l_IO_FS_readFile(v_path_3387_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3418_; 
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3392_ = v___x_3389_;
v_isShared_3393_ = v_isSharedCheck_3418_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3389_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3418_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v_a_3395_; lean_object* v___x_3405_; 
v___x_3405_ = l_Lean_Json_parse(v_a_3390_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref(v___x_3405_);
v_a_3395_ = v_a_3406_;
goto v___jp_3394_;
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3408_; 
v_a_3407_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3407_);
lean_dec_ref(v___x_3405_);
v___x_3408_ = l_Lean_instFromJsonModuleSetup_fromJson(v_a_3407_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_a_3409_);
lean_dec_ref(v___x_3408_);
v_a_3395_ = v_a_3409_;
goto v___jp_3394_;
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_del_object(v___x_3392_);
v_a_3410_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3408_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3408_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
lean_ctor_set_tag(v___x_3412_, 0);
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
v___jp_3394_:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3403_; 
v___x_3396_ = ((lean_object*)(l_Lean_ModuleSetup_load___closed__0));
v___x_3397_ = lean_string_append(v___x_3396_, v_path_3387_);
v___x_3398_ = ((lean_object*)(l_Lean_instFromJsonImport_fromJson___closed__9));
v___x_3399_ = lean_string_append(v___x_3397_, v___x_3398_);
v___x_3400_ = lean_string_append(v___x_3399_, v_a_3395_);
lean_dec_ref(v_a_3395_);
v___x_3401_ = lean_mk_io_user_error(v___x_3400_);
if (v_isShared_3393_ == 0)
{
lean_ctor_set_tag(v___x_3392_, 1);
lean_ctor_set(v___x_3392_, 0, v___x_3401_);
v___x_3403_ = v___x_3392_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3401_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
v_a_3419_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3389_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3389_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
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
}
LEAN_EXPORT lean_object* l_Lean_ModuleSetup_load___boxed(lean_object* v_path_3427_, lean_object* v_a_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l_Lean_ModuleSetup_load(v_path_3427_);
lean_dec_ref(v_path_3427_);
return v_res_3429_;
}
}
lean_object* runtime_initialize_Lean_Data_Json_Parser(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_LeanOptions(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Setup(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
