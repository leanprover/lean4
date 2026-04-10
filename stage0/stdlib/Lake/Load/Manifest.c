// Lean compiler output
// Module: Lake.Load.Manifest
// Imports: public import Lake.Util.Version public import Lake.Config.Defaults import Lake.Util.Error public import Lake.Util.FilePath import Lake.Util.JsonObject import Init.Data.Option.Coe
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* l_Lake_JsonObject_getJson_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultManifestFile;
extern lean_object* l_Lake_defaultConfigFile;
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lake_StdVer_compare(lean_object*, lean_object*);
lean_object* l_Lean_Json_getTag_x3f(lean_object*);
lean_object* l_Lean_Json_parseCtorFields(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lake_SemVerCore_toString(lean_object*);
uint8_t l_Lake_instOrdSemVerCore_ord(lean_object*, lean_object*);
lean_object* l_Lake_StdVer_toString(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lake_StdVer_parseM(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_Manifest_version___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Manifest_version___closed__0 = (const lean_object*)&l_Lake_Manifest_version___closed__0_value;
static const lean_string_object l_Lake_Manifest_version___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_Manifest_version___closed__1 = (const lean_object*)&l_Lake_Manifest_version___closed__1_value;
static const lean_ctor_object l_Lake_Manifest_version___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Manifest_version___closed__0_value),((lean_object*)&l_Lake_Manifest_version___closed__1_value)}};
static const lean_object* l_Lake_Manifest_version___closed__2 = (const lean_object*)&l_Lake_Manifest_version___closed__2_value;
LEAN_EXPORT const lean_object* l_Lake_Manifest_version = (const lean_object*)&l_Lake_Manifest_version___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_path_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_path_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_git_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_git_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[anonymous]"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "expected a `Name`, got '"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "expected a `NameMap`, got '"};
static const lean_object* l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0___closed__0 = (const lean_object*)&l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0(lean_object*);
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "no inductive tag found"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__0 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__0_value;
static const lean_ctor_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__0_value)}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__1 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__1_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "path"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "git"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "no inductive constructor matched"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__4 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__4_value;
static const lean_ctor_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__4_value)}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__5 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__5_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6_value;
static const lean_ctor_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__7 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__7_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "opts"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__8 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__8_value;
static const lean_ctor_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__8_value),LEAN_SCALAR_PTR_LITERAL(49, 15, 216, 57, 127, 228, 200, 93)}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__9 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__9_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "inherited"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10_value;
static const lean_ctor_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10_value),LEAN_SCALAR_PTR_LITERAL(5, 243, 84, 167, 125, 155, 180, 170)}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__11 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__11_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "url"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12_value;
static const lean_ctor_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12_value),LEAN_SCALAR_PTR_LITERAL(223, 8, 114, 234, 1, 186, 24, 188)}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__13 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__13_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rev"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14_value;
static const lean_ctor_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14_value),LEAN_SCALAR_PTR_LITERAL(215, 226, 195, 78, 237, 95, 37, 186)}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__15 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__15_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "inputRev\?"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__16 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__16_value;
static const lean_ctor_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__16_value),LEAN_SCALAR_PTR_LITERAL(35, 252, 185, 60, 100, 164, 29, 176)}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__17 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__17_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "subDir\?"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__18 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__18_value;
static const lean_ctor_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__18_value),LEAN_SCALAR_PTR_LITERAL(200, 131, 32, 198, 225, 97, 240, 33)}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__19 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__19_value;
static const lean_array_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__7_value),((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__9_value),((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__11_value),((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__13_value),((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__15_value),((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__17_value),((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__19_value)}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__20 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__20_value;
static const lean_ctor_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__20_value)}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__21 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__21_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dir"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22_value;
static const lean_ctor_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22_value),LEAN_SCALAR_PTR_LITERAL(133, 174, 87, 196, 58, 217, 0, 187)}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__23 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__23_value;
static const lean_array_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__7_value),((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__9_value),((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__11_value),((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__23_value)}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__24 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__24_value;
static const lean_ctor_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__24_value)}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__25 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__25_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson(lean_object*);
static const lean_closure_object l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6___closed__0 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6___closed__0_value;
LEAN_EXPORT lean_object* l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Data.DTreeMap.Internal.Balancing"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__6_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6___closed__0 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedPackageEntryV6_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lake_Manifest_version___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_instInhabitedPackageEntryV6_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedPackageEntryV6_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedPackageEntryV6_default = (const lean_object*)&l_Lake_instInhabitedPackageEntryV6_default___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6 = (const lean_object*)&l_Lake_instInhabitedPackageEntryV6_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_path_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_path_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_git_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_git_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lake_instInhabitedPackageEntrySrc_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Manifest_version___closed__1_value)}};
static const lean_object* l_Lake_instInhabitedPackageEntrySrc_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedPackageEntrySrc_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedPackageEntrySrc_default = (const lean_object*)&l_Lake_instInhabitedPackageEntrySrc_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedPackageEntrySrc = (const lean_object*)&l_Lake_instInhabitedPackageEntrySrc_default___closed__0_value;
static lean_once_cell_t l_Lake_instInhabitedPackageEntry_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPackageEntry_default___closed__0;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageEntry_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageEntry;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_prettyName(lean_object*);
static const lean_string_object l_Lake_PackageEntry_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "scope"};
static const lean_object* l_Lake_PackageEntry_toJson___closed__0 = (const lean_object*)&l_Lake_PackageEntry_toJson___closed__0_value;
static const lean_string_object l_Lake_PackageEntry_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configFile"};
static const lean_object* l_Lake_PackageEntry_toJson___closed__1 = (const lean_object*)&l_Lake_PackageEntry_toJson___closed__1_value;
static const lean_string_object l_Lake_PackageEntry_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "manifestFile"};
static const lean_object* l_Lake_PackageEntry_toJson___closed__2 = (const lean_object*)&l_Lake_PackageEntry_toJson___closed__2_value;
static const lean_string_object l_Lake_PackageEntry_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l_Lake_PackageEntry_toJson___closed__3 = (const lean_object*)&l_Lake_PackageEntry_toJson___closed__3_value;
static const lean_ctor_object l_Lake_PackageEntry_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2_value)}};
static const lean_object* l_Lake_PackageEntry_toJson___closed__4 = (const lean_object*)&l_Lake_PackageEntry_toJson___closed__4_value;
static const lean_ctor_object l_Lake_PackageEntry_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageEntry_toJson___closed__3_value),((lean_object*)&l_Lake_PackageEntry_toJson___closed__4_value)}};
static const lean_object* l_Lake_PackageEntry_toJson___closed__5 = (const lean_object*)&l_Lake_PackageEntry_toJson___closed__5_value;
static const lean_ctor_object l_Lake_PackageEntry_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3_value)}};
static const lean_object* l_Lake_PackageEntry_toJson___closed__6 = (const lean_object*)&l_Lake_PackageEntry_toJson___closed__6_value;
static const lean_ctor_object l_Lake_PackageEntry_toJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageEntry_toJson___closed__3_value),((lean_object*)&l_Lake_PackageEntry_toJson___closed__6_value)}};
static const lean_object* l_Lake_PackageEntry_toJson___closed__7 = (const lean_object*)&l_Lake_PackageEntry_toJson___closed__7_value;
static const lean_string_object l_Lake_PackageEntry_toJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "inputRev"};
static const lean_object* l_Lake_PackageEntry_toJson___closed__8 = (const lean_object*)&l_Lake_PackageEntry_toJson___closed__8_value;
static const lean_string_object l_Lake_PackageEntry_toJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "subDir"};
static const lean_object* l_Lake_PackageEntry_toJson___closed__9 = (const lean_object*)&l_Lake_PackageEntry_toJson___closed__9_value;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_toJson(lean_object*);
static const lean_closure_object l_Lake_PackageEntry_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageEntry_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageEntry_instToJson___closed__0 = (const lean_object*)&l_Lake_PackageEntry_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_PackageEntry_instToJson = (const lean_object*)&l_Lake_PackageEntry_instToJson___closed__0_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "package entry: "};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0___boxed(lean_object*);
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "property not found: name"};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__0 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__0_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "name: "};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__1 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__1_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "package entry '"};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__2 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__2_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "': "};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__3 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__3_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "subDir: "};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__4 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__4_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "unknown package entry type '"};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__5 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__5_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "property not found: url"};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__6 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__6_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "url: "};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__7 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__7_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "property not found: rev"};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__8 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__8_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "rev: "};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__9 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__9_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "inputRev: "};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__10 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__10_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "property not found: dir"};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__11 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__11_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dir: "};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__12 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__12_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "manifestFile: "};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__13 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__13_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "property not found: type"};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__14 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__14_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "type: "};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__15 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__15_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "property not found: inherited"};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__16 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__16_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "inherited: "};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__17 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__17_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "configFile: "};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__18 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__18_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "scope: "};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__19 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__19_value;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lake_PackageEntry_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageEntry_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageEntry_instFromJson___closed__0 = (const lean_object*)&l_Lake_PackageEntry_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_PackageEntry_instFromJson = (const lean_object*)&l_Lake_PackageEntry_instFromJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setInherited(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setConfigFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setManifestFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_inDirectory(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_addPackage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_Manifest_toJson_spec__0(lean_object*);
static const lean_string_object l_Lake_Manifest_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l_Lake_Manifest_toJson___closed__0 = (const lean_object*)&l_Lake_Manifest_toJson___closed__0_value;
static lean_once_cell_t l_Lake_Manifest_toJson___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Manifest_toJson___closed__1;
static lean_once_cell_t l_Lake_Manifest_toJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Manifest_toJson___closed__2;
static lean_once_cell_t l_Lake_Manifest_toJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Manifest_toJson___closed__3;
static const lean_string_object l_Lake_Manifest_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fixedToolchain"};
static const lean_object* l_Lake_Manifest_toJson___closed__4 = (const lean_object*)&l_Lake_Manifest_toJson___closed__4_value;
static const lean_string_object l_Lake_Manifest_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "lakeDir"};
static const lean_object* l_Lake_Manifest_toJson___closed__5 = (const lean_object*)&l_Lake_Manifest_toJson___closed__5_value;
static const lean_string_object l_Lake_Manifest_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "packagesDir"};
static const lean_object* l_Lake_Manifest_toJson___closed__6 = (const lean_object*)&l_Lake_Manifest_toJson___closed__6_value;
static const lean_string_object l_Lake_Manifest_toJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "packages"};
static const lean_object* l_Lake_Manifest_toJson___closed__7 = (const lean_object*)&l_Lake_Manifest_toJson___closed__7_value;
LEAN_EXPORT lean_object* l_Lake_Manifest_toJson(lean_object*);
static const lean_closure_object l_Lake_Manifest_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Manifest_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Manifest_instToJson___closed__0 = (const lean_object*)&l_Lake_Manifest_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Manifest_instToJson = (const lean_object*)&l_Lake_Manifest_instToJson___closed__0_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "incompatible manifest version '"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__0 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__0_value;
static const lean_ctor_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__1 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__1_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "schema version '"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__2 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__2_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "' is of a higher major version than this Lake's '"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__3 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__3_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "'; you may need to update your 'lean-toolchain'"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "invalid version '"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__5 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__5_value;
static lean_once_cell_t l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6;
static const lean_closure_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StdVer_parseM, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "schemaVersion"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "property not found: schemaVersion"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__9 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__9_value;
static const lean_ctor_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__9_value)}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__10 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__0 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__0_value;
static const lean_array_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__1 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__1_value;
static const lean_ctor_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__1_value)}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__2 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__2_value;
static const lean_ctor_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(7) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__3 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__3_value;
static const lean_ctor_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__3_value),((lean_object*)&l_Lake_Manifest_version___closed__1_value)}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__4 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__4_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "packages: "};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1___boxed(lean_object*);
static const lean_string_object l_Lake_Manifest_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "packagesDir: "};
static const lean_object* l_Lake_Manifest_fromJson_x3f___closed__0 = (const lean_object*)&l_Lake_Manifest_fromJson_x3f___closed__0_value;
static const lean_string_object l_Lake_Manifest_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "lakeDir: "};
static const lean_object* l_Lake_Manifest_fromJson_x3f___closed__1 = (const lean_object*)&l_Lake_Manifest_fromJson_x3f___closed__1_value;
static const lean_string_object l_Lake_Manifest_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fixedToolchain: "};
static const lean_object* l_Lake_Manifest_fromJson_x3f___closed__2 = (const lean_object*)&l_Lake_Manifest_fromJson_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_Manifest_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lake_Manifest_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Manifest_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Manifest_instFromJson___closed__0 = (const lean_object*)&l_Lake_Manifest_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Manifest_instFromJson = (const lean_object*)&l_Lake_Manifest_instFromJson___closed__0_value;
static const lean_string_object l_Lake_Manifest_parse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "invalid JSON: "};
static const lean_object* l_Lake_Manifest_parse___closed__0 = (const lean_object*)&l_Lake_Manifest_parse___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Manifest_parse(lean_object*);
static const lean_string_object l_Lake_Manifest_load___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lake_Manifest_load___closed__0 = (const lean_object*)&l_Lake_Manifest_load___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Manifest_load(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_load___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_save(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_save___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_decodeEntries(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_parseEntries(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_loadEntries(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_loadEntries___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Manifest_saveEntries___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Manifest_saveEntries___closed__0;
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorIdx(lean_object* v_x_10_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v___x_11_; 
v___x_11_ = lean_unsigned_to_nat(0u);
return v___x_11_;
}
else
{
lean_object* v___x_12_; 
v___x_12_ = lean_unsigned_to_nat(1u);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorIdx___boxed(lean_object* v_x_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorIdx(v_x_13_);
lean_dec_ref(v_x_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(lean_object* v_t_15_, lean_object* v_k_16_){
_start:
{
if (lean_obj_tag(v_t_15_) == 0)
{
lean_object* v_name_17_; lean_object* v_opts_18_; uint8_t v_inherited_19_; lean_object* v_dir_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v_name_17_ = lean_ctor_get(v_t_15_, 0);
lean_inc(v_name_17_);
v_opts_18_ = lean_ctor_get(v_t_15_, 1);
lean_inc(v_opts_18_);
v_inherited_19_ = lean_ctor_get_uint8(v_t_15_, sizeof(void*)*3);
v_dir_20_ = lean_ctor_get(v_t_15_, 2);
lean_inc_ref(v_dir_20_);
lean_dec_ref(v_t_15_);
v___x_21_ = lean_box(v_inherited_19_);
v___x_22_ = lean_apply_4(v_k_16_, v_name_17_, v_opts_18_, v___x_21_, v_dir_20_);
return v___x_22_;
}
else
{
lean_object* v_name_23_; lean_object* v_opts_24_; uint8_t v_inherited_25_; lean_object* v_url_26_; lean_object* v_rev_27_; lean_object* v_inputRev_x3f_28_; lean_object* v_subDir_x3f_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v_name_23_ = lean_ctor_get(v_t_15_, 0);
lean_inc(v_name_23_);
v_opts_24_ = lean_ctor_get(v_t_15_, 1);
lean_inc(v_opts_24_);
v_inherited_25_ = lean_ctor_get_uint8(v_t_15_, sizeof(void*)*6);
v_url_26_ = lean_ctor_get(v_t_15_, 2);
lean_inc_ref(v_url_26_);
v_rev_27_ = lean_ctor_get(v_t_15_, 3);
lean_inc_ref(v_rev_27_);
v_inputRev_x3f_28_ = lean_ctor_get(v_t_15_, 4);
lean_inc(v_inputRev_x3f_28_);
v_subDir_x3f_29_ = lean_ctor_get(v_t_15_, 5);
lean_inc(v_subDir_x3f_29_);
lean_dec_ref(v_t_15_);
v___x_30_ = lean_box(v_inherited_25_);
v___x_31_ = lean_apply_7(v_k_16_, v_name_23_, v_opts_24_, v___x_30_, v_url_26_, v_rev_27_, v_inputRev_x3f_28_, v_subDir_x3f_29_);
return v___x_31_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim(lean_object* v_motive_32_, lean_object* v_ctorIdx_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_k_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(v_t_34_, v_k_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___boxed(lean_object* v_motive_38_, lean_object* v_ctorIdx_39_, lean_object* v_t_40_, lean_object* v_h_41_, lean_object* v_k_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim(v_motive_38_, v_ctorIdx_39_, v_t_40_, v_h_41_, v_k_42_);
lean_dec(v_ctorIdx_39_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_path_elim___redArg(lean_object* v_t_44_, lean_object* v_path_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(v_t_44_, v_path_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_path_elim(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_path_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(v_t_48_, v_path_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_git_elim___redArg(lean_object* v_t_52_, lean_object* v_git_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(v_t_52_, v_git_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_git_elim(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_git_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(v_t_56_, v_git_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(lean_object* v_x_62_){
_start:
{
if (lean_obj_tag(v_x_62_) == 0)
{
lean_object* v___x_63_; 
v___x_63_ = ((lean_object*)(l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0));
return v___x_63_;
}
else
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_Json_getStr_x3f(v_x_62_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v_a_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_72_; 
v_a_65_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_72_ == 0)
{
v___x_67_ = v___x_64_;
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_a_65_);
lean_dec(v___x_64_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_70_; 
if (v_isShared_68_ == 0)
{
v___x_70_ = v___x_67_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_a_65_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
else
{
lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_81_; 
v_a_73_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_81_ == 0)
{
v___x_75_ = v___x_64_;
v_isShared_76_ = v_isSharedCheck_81_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_64_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_81_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; lean_object* v___x_79_; 
v___x_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_77_, 0, v_a_73_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 0, v___x_77_);
v___x_79_ = v___x_75_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v___x_77_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(lean_object* v_x_82_){
_start:
{
if (lean_obj_tag(v_x_82_) == 0)
{
lean_object* v___x_83_; 
v___x_83_ = ((lean_object*)(l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0));
return v___x_83_;
}
else
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_Json_getStr_x3f(v_x_82_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_92_; 
v_a_85_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_92_ == 0)
{
v___x_87_ = v___x_84_;
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v___x_84_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_90_; 
if (v_isShared_88_ == 0)
{
v___x_90_ = v___x_87_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_a_85_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
else
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_101_; 
v_a_93_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_101_ == 0)
{
v___x_95_ = v___x_84_;
v_isShared_96_ = v_isSharedCheck_101_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_84_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_101_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_97_; lean_object* v___x_99_; 
v___x_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_97_, 0, v_a_93_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_97_);
v___x_99_ = v___x_95_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_97_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0(lean_object* v_init_105_, lean_object* v_x_106_){
_start:
{
if (lean_obj_tag(v_x_106_) == 0)
{
lean_object* v_k_107_; lean_object* v_v_108_; lean_object* v_l_109_; lean_object* v_r_110_; lean_object* v___x_111_; 
v_k_107_ = lean_ctor_get(v_x_106_, 1);
lean_inc(v_k_107_);
v_v_108_ = lean_ctor_get(v_x_106_, 2);
lean_inc(v_v_108_);
v_l_109_ = lean_ctor_get(v_x_106_, 3);
lean_inc(v_l_109_);
v_r_110_ = lean_ctor_get(v_x_106_, 4);
lean_inc(v_r_110_);
lean_dec_ref(v_x_106_);
v___x_111_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0(v_init_105_, v_l_109_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_dec(v_r_110_);
lean_dec(v_v_108_);
lean_dec(v_k_107_);
return v___x_111_;
}
else
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_152_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_152_ == 0)
{
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_152_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_152_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__0));
v___x_117_ = lean_string_dec_eq(v_k_107_, v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v_n_118_; uint8_t v___x_119_; 
lean_inc(v_k_107_);
v_n_118_ = l_String_toName(v_k_107_);
v___x_119_ = l_Lean_Name_isAnonymous(v_n_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; 
lean_del_object(v___x_114_);
lean_dec(v_k_107_);
v___x_120_ = l_Lean_Json_getStr_x3f(v_v_108_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
lean_dec(v_n_118_);
lean_dec(v_a_112_);
lean_dec(v_r_110_);
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
else
{
lean_object* v_a_129_; lean_object* v___x_130_; 
v_a_129_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_a_129_);
lean_dec_ref(v___x_120_);
v___x_130_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_118_, v_a_129_, v_a_112_);
v_init_105_ = v___x_130_;
v_x_106_ = v_r_110_;
goto _start;
}
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
lean_dec(v_n_118_);
lean_dec(v_a_112_);
lean_dec(v_r_110_);
lean_dec(v_v_108_);
v___x_132_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__1));
v___x_133_ = lean_string_append(v___x_132_, v_k_107_);
lean_dec(v_k_107_);
v___x_134_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_135_ = lean_string_append(v___x_133_, v___x_134_);
if (v_isShared_115_ == 0)
{
lean_ctor_set_tag(v___x_114_, 0);
lean_ctor_set(v___x_114_, 0, v___x_135_);
v___x_137_ = v___x_114_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v___x_139_; 
lean_del_object(v___x_114_);
lean_dec(v_k_107_);
v___x_139_ = l_Lean_Json_getStr_x3f(v_v_108_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
lean_dec(v_a_112_);
lean_dec(v_r_110_);
v_a_140_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v___x_139_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_139_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
else
{
lean_object* v_a_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v_a_148_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_a_148_);
lean_dec_ref(v___x_139_);
v___x_149_ = lean_box(0);
v___x_150_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_149_, v_a_148_, v_a_112_);
v_init_105_ = v___x_150_;
v_x_106_ = v_r_110_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_153_; 
v___x_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_153_, 0, v_init_105_);
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0(lean_object* v_x_155_){
_start:
{
if (lean_obj_tag(v_x_155_) == 5)
{
lean_object* v_kvPairs_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_kvPairs_156_ = lean_ctor_get(v_x_155_, 0);
lean_inc(v_kvPairs_156_);
lean_dec_ref(v_x_155_);
v___x_157_ = lean_box(1);
v___x_158_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0(v___x_157_, v_kvPairs_156_);
return v___x_158_;
}
else
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_159_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0___closed__0));
v___x_160_ = lean_unsigned_to_nat(80u);
v___x_161_ = l_Lean_Json_pretty(v_x_155_, v___x_160_);
v___x_162_ = lean_string_append(v___x_159_, v___x_161_);
lean_dec_ref(v___x_161_);
v___x_163_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_164_ = lean_string_append(v___x_162_, v___x_163_);
v___x_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson(lean_object* v_json_228_){
_start:
{
lean_object* v___x_229_; 
lean_inc(v_json_228_);
v___x_229_ = l_Lean_Json_getTag_x3f(v_json_228_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v___x_230_; 
lean_dec(v_json_228_);
v___x_230_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__1));
return v___x_230_;
}
else
{
lean_object* v_val_231_; lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v_val_231_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_val_231_);
lean_dec_ref(v___x_229_);
v___x_232_ = lean_box(0);
v___x_233_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2));
v___x_234_ = lean_string_dec_eq(v_val_231_, v___x_233_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_235_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3));
v___x_236_ = lean_string_dec_eq(v_val_231_, v___x_235_);
lean_dec(v_val_231_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; 
lean_dec(v_json_228_);
v___x_237_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__5));
return v___x_237_;
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = lean_unsigned_to_nat(7u);
v___x_239_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__21));
v___x_240_ = l_Lean_Json_parseCtorFields(v_json_228_, v___x_235_, v___x_238_, v___x_239_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_248_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v___x_240_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_240_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_241_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
else
{
lean_object* v_a_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_a_249_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_a_249_);
lean_dec_ref(v___x_240_);
v___x_250_ = lean_unsigned_to_nat(0u);
v___x_251_ = lean_array_get_borrowed(v___x_232_, v_a_249_, v___x_250_);
lean_inc(v___x_251_);
v___x_252_ = l_Lean_Name_fromJson_x3f(v___x_251_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec(v_a_249_);
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
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
lean_object* v_a_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_a_261_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_261_);
lean_dec_ref(v___x_252_);
v___x_262_ = lean_unsigned_to_nat(1u);
v___x_263_ = lean_array_get_borrowed(v___x_232_, v_a_249_, v___x_262_);
lean_inc(v___x_263_);
v___x_264_ = l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0(v___x_263_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
lean_dec(v_a_261_);
lean_dec(v_a_249_);
v_a_265_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_264_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_264_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_a_273_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_273_);
lean_dec_ref(v___x_264_);
v___x_274_ = lean_unsigned_to_nat(2u);
v___x_275_ = lean_array_get_borrowed(v___x_232_, v_a_249_, v___x_274_);
v___x_276_ = l_Lean_Json_getBool_x3f(v___x_275_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
lean_dec(v_a_273_);
lean_dec(v_a_261_);
lean_dec(v_a_249_);
v_a_277_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_276_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_276_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
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
lean_object* v_a_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_a_285_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_285_);
lean_dec_ref(v___x_276_);
v___x_286_ = lean_unsigned_to_nat(3u);
v___x_287_ = lean_array_get_borrowed(v___x_232_, v_a_249_, v___x_286_);
lean_inc(v___x_287_);
v___x_288_ = l_Lean_Json_getStr_x3f(v___x_287_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_dec(v_a_285_);
lean_dec(v_a_273_);
lean_dec(v_a_261_);
lean_dec(v_a_249_);
v_a_289_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_a_297_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_a_297_);
lean_dec_ref(v___x_288_);
v___x_298_ = lean_unsigned_to_nat(4u);
v___x_299_ = lean_array_get_borrowed(v___x_232_, v_a_249_, v___x_298_);
lean_inc(v___x_299_);
v___x_300_ = l_Lean_Json_getStr_x3f(v___x_299_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
lean_dec(v_a_297_);
lean_dec(v_a_285_);
lean_dec(v_a_273_);
lean_dec(v_a_261_);
lean_dec(v_a_249_);
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
else
{
lean_object* v_a_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v_a_309_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_309_);
lean_dec_ref(v___x_300_);
v___x_310_ = lean_unsigned_to_nat(5u);
v___x_311_ = lean_array_get_borrowed(v___x_232_, v_a_249_, v___x_310_);
lean_inc(v___x_311_);
v___x_312_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(v___x_311_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_dec(v_a_309_);
lean_dec(v_a_297_);
lean_dec(v_a_285_);
lean_dec(v_a_273_);
lean_dec(v_a_261_);
lean_dec(v_a_249_);
v_a_313_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_312_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_312_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
else
{
lean_object* v_a_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v_a_321_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_321_);
lean_dec_ref(v___x_312_);
v___x_322_ = lean_unsigned_to_nat(6u);
v___x_323_ = lean_array_get(v___x_232_, v_a_249_, v___x_322_);
lean_dec(v_a_249_);
v___x_324_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v___x_323_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_dec(v_a_321_);
lean_dec(v_a_309_);
lean_dec(v_a_297_);
lean_dec(v_a_285_);
lean_dec(v_a_273_);
lean_dec(v_a_261_);
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_342_; 
v_a_333_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_342_ == 0)
{
v___x_335_ = v___x_324_;
v_isShared_336_ = v_isSharedCheck_342_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_324_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_342_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; uint8_t v___x_338_; lean_object* v___x_340_; 
v___x_337_ = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(v___x_337_, 0, v_a_261_);
lean_ctor_set(v___x_337_, 1, v_a_273_);
lean_ctor_set(v___x_337_, 2, v_a_297_);
lean_ctor_set(v___x_337_, 3, v_a_309_);
lean_ctor_set(v___x_337_, 4, v_a_321_);
lean_ctor_set(v___x_337_, 5, v_a_333_);
v___x_338_ = lean_unbox(v_a_285_);
lean_dec(v_a_285_);
lean_ctor_set_uint8(v___x_337_, sizeof(void*)*6, v___x_338_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_337_);
v___x_340_ = v___x_335_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_337_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
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
else
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
lean_dec(v_val_231_);
v___x_343_ = lean_unsigned_to_nat(4u);
v___x_344_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__25));
v___x_345_ = l_Lean_Json_parseCtorFields(v_json_228_, v___x_233_, v___x_343_, v___x_344_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_345_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_345_);
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
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_a_354_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_354_);
lean_dec_ref(v___x_345_);
v___x_355_ = lean_unsigned_to_nat(0u);
v___x_356_ = lean_array_get_borrowed(v___x_232_, v_a_354_, v___x_355_);
lean_inc(v___x_356_);
v___x_357_ = l_Lean_Name_fromJson_x3f(v___x_356_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec(v_a_354_);
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v_a_366_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_366_);
lean_dec_ref(v___x_357_);
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = lean_array_get_borrowed(v___x_232_, v_a_354_, v___x_367_);
lean_inc(v___x_368_);
v___x_369_ = l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0(v___x_368_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec(v_a_366_);
lean_dec(v_a_354_);
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
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
lean_object* v_a_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_a_378_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_a_378_);
lean_dec_ref(v___x_369_);
v___x_379_ = lean_unsigned_to_nat(2u);
v___x_380_ = lean_array_get_borrowed(v___x_232_, v_a_354_, v___x_379_);
v___x_381_ = l_Lean_Json_getBool_x3f(v___x_380_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_dec(v_a_378_);
lean_dec(v_a_366_);
lean_dec(v_a_354_);
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
else
{
lean_object* v_a_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v_a_390_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_a_390_);
lean_dec_ref(v___x_381_);
v___x_391_ = lean_unsigned_to_nat(3u);
v___x_392_ = lean_array_get(v___x_232_, v_a_354_, v___x_391_);
lean_dec(v_a_354_);
v___x_393_ = l_Lean_Json_getStr_x3f(v___x_392_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
lean_dec(v_a_390_);
lean_dec(v_a_378_);
lean_dec(v_a_366_);
v_a_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_411_; 
v_a_402_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_411_ == 0)
{
v___x_404_ = v___x_393_;
v_isShared_405_ = v_isSharedCheck_411_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_393_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_411_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; uint8_t v___x_407_; lean_object* v___x_409_; 
v___x_406_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_406_, 0, v_a_366_);
lean_ctor_set(v___x_406_, 1, v_a_378_);
lean_ctor_set(v___x_406_, 2, v_a_402_);
v___x_407_ = lean_unbox(v_a_390_);
lean_dec(v_a_390_);
lean_ctor_set_uint8(v___x_406_, sizeof(void*)*3, v___x_407_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_406_);
v___x_409_ = v___x_404_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_406_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
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
LEAN_EXPORT lean_object* l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__1(lean_object* v_x_414_){
_start:
{
if (lean_obj_tag(v_x_414_) == 0)
{
lean_object* v___x_415_; 
v___x_415_ = lean_box(0);
return v___x_415_;
}
else
{
lean_object* v_val_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
v_val_416_ = lean_ctor_get(v_x_414_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v_x_414_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v_x_414_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_val_416_);
lean_dec(v_x_414_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 3);
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_val_416_);
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
LEAN_EXPORT lean_object* l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(lean_object* v_x_424_){
_start:
{
if (lean_obj_tag(v_x_424_) == 0)
{
lean_object* v___x_425_; 
v___x_425_ = lean_box(0);
return v___x_425_;
}
else
{
lean_object* v_val_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_434_; 
v_val_426_ = lean_ctor_get(v_x_424_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v_x_424_);
if (v_isSharedCheck_434_ == 0)
{
v___x_428_ = v_x_424_;
v_isShared_429_ = v_isSharedCheck_434_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_val_426_);
lean_dec(v_x_424_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_434_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_430_ = l_Lake_mkRelPathString(v_val_426_);
if (v_isShared_429_ == 0)
{
lean_ctor_set_tag(v___x_428_, 3);
lean_ctor_set(v___x_428_, 0, v___x_430_);
v___x_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(lean_object* v_msg_435_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_box(1);
v___x_437_ = lean_panic_fn_borrowed(v___x_436_, v_msg_435_);
return v___x_437_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_441_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__2));
v___x_442_ = lean_unsigned_to_nat(35u);
v___x_443_ = lean_unsigned_to_nat(276u);
v___x_444_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__1));
v___x_445_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__0));
v___x_446_ = l_mkPanicMessageWithDecl(v___x_445_, v___x_444_, v___x_443_, v___x_442_, v___x_441_);
return v___x_446_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_447_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__2));
v___x_448_ = lean_unsigned_to_nat(21u);
v___x_449_ = lean_unsigned_to_nat(277u);
v___x_450_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__1));
v___x_451_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__0));
v___x_452_ = l_mkPanicMessageWithDecl(v___x_451_, v___x_450_, v___x_449_, v___x_448_, v___x_447_);
return v___x_452_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_455_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__6));
v___x_456_ = lean_unsigned_to_nat(35u);
v___x_457_ = lean_unsigned_to_nat(182u);
v___x_458_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__5));
v___x_459_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__0));
v___x_460_ = l_mkPanicMessageWithDecl(v___x_459_, v___x_458_, v___x_457_, v___x_456_, v___x_455_);
return v___x_460_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_461_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__6));
v___x_462_ = lean_unsigned_to_nat(21u);
v___x_463_ = lean_unsigned_to_nat(183u);
v___x_464_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__5));
v___x_465_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__0));
v___x_466_ = l_mkPanicMessageWithDecl(v___x_465_, v___x_464_, v___x_463_, v___x_462_, v___x_461_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(lean_object* v_k_467_, lean_object* v_v_468_, lean_object* v_t_469_){
_start:
{
if (lean_obj_tag(v_t_469_) == 0)
{
lean_object* v_size_470_; lean_object* v_k_471_; lean_object* v_v_472_; lean_object* v_l_473_; lean_object* v_r_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_831_; 
v_size_470_ = lean_ctor_get(v_t_469_, 0);
v_k_471_ = lean_ctor_get(v_t_469_, 1);
v_v_472_ = lean_ctor_get(v_t_469_, 2);
v_l_473_ = lean_ctor_get(v_t_469_, 3);
v_r_474_ = lean_ctor_get(v_t_469_, 4);
v_isSharedCheck_831_ = !lean_is_exclusive(v_t_469_);
if (v_isSharedCheck_831_ == 0)
{
v___x_476_ = v_t_469_;
v_isShared_477_ = v_isSharedCheck_831_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_r_474_);
lean_inc(v_l_473_);
lean_inc(v_v_472_);
lean_inc(v_k_471_);
lean_inc(v_size_470_);
lean_dec(v_t_469_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_831_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
uint8_t v___x_478_; 
v___x_478_ = lean_string_dec_lt(v_k_467_, v_k_471_);
if (v___x_478_ == 0)
{
uint8_t v___x_479_; 
v___x_479_ = lean_string_dec_eq(v_k_467_, v_k_471_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; 
lean_dec(v_size_470_);
v___x_480_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(v_k_467_, v_v_468_, v_r_474_);
if (lean_obj_tag(v_l_473_) == 0)
{
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_size_481_; lean_object* v_size_482_; lean_object* v_k_483_; lean_object* v_v_484_; lean_object* v_l_485_; lean_object* v_r_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_size_481_ = lean_ctor_get(v_l_473_, 0);
v_size_482_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_size_482_);
v_k_483_ = lean_ctor_get(v___x_480_, 1);
lean_inc(v_k_483_);
v_v_484_ = lean_ctor_get(v___x_480_, 2);
lean_inc(v_v_484_);
v_l_485_ = lean_ctor_get(v___x_480_, 3);
lean_inc(v_l_485_);
v_r_486_ = lean_ctor_get(v___x_480_, 4);
lean_inc(v_r_486_);
v___x_487_ = lean_unsigned_to_nat(3u);
v___x_488_ = lean_nat_mul(v___x_487_, v_size_481_);
v___x_489_ = lean_nat_dec_lt(v___x_488_, v_size_482_);
lean_dec(v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_494_; 
lean_dec(v_r_486_);
lean_dec(v_l_485_);
lean_dec(v_v_484_);
lean_dec(v_k_483_);
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = lean_nat_add(v___x_490_, v_size_481_);
v___x_492_ = lean_nat_add(v___x_491_, v_size_482_);
lean_dec(v_size_482_);
lean_dec(v___x_491_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_480_);
lean_ctor_set(v___x_476_, 0, v___x_492_);
v___x_494_ = v___x_476_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_495_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_495_, 3, v_l_473_);
lean_ctor_set(v_reuseFailAlloc_495_, 4, v___x_480_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
else
{
lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_565_; 
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_565_ == 0)
{
lean_object* v_unused_566_; lean_object* v_unused_567_; lean_object* v_unused_568_; lean_object* v_unused_569_; lean_object* v_unused_570_; 
v_unused_566_ = lean_ctor_get(v___x_480_, 4);
lean_dec(v_unused_566_);
v_unused_567_ = lean_ctor_get(v___x_480_, 3);
lean_dec(v_unused_567_);
v_unused_568_ = lean_ctor_get(v___x_480_, 2);
lean_dec(v_unused_568_);
v_unused_569_ = lean_ctor_get(v___x_480_, 1);
lean_dec(v_unused_569_);
v_unused_570_ = lean_ctor_get(v___x_480_, 0);
lean_dec(v_unused_570_);
v___x_497_ = v___x_480_;
v_isShared_498_ = v_isSharedCheck_565_;
goto v_resetjp_496_;
}
else
{
lean_dec(v___x_480_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_565_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
if (lean_obj_tag(v_l_485_) == 0)
{
if (lean_obj_tag(v_r_486_) == 0)
{
lean_object* v_size_499_; lean_object* v_k_500_; lean_object* v_v_501_; lean_object* v_l_502_; lean_object* v_r_503_; lean_object* v_size_504_; lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v_size_499_ = lean_ctor_get(v_l_485_, 0);
v_k_500_ = lean_ctor_get(v_l_485_, 1);
v_v_501_ = lean_ctor_get(v_l_485_, 2);
v_l_502_ = lean_ctor_get(v_l_485_, 3);
v_r_503_ = lean_ctor_get(v_l_485_, 4);
v_size_504_ = lean_ctor_get(v_r_486_, 0);
v___x_505_ = lean_unsigned_to_nat(2u);
v___x_506_ = lean_nat_mul(v___x_505_, v_size_504_);
v___x_507_ = lean_nat_dec_lt(v_size_499_, v___x_506_);
lean_dec(v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_536_; 
lean_inc(v_r_503_);
lean_inc(v_l_502_);
lean_inc(v_v_501_);
lean_inc(v_k_500_);
v_isSharedCheck_536_ = !lean_is_exclusive(v_l_485_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; lean_object* v_unused_538_; lean_object* v_unused_539_; lean_object* v_unused_540_; lean_object* v_unused_541_; 
v_unused_537_ = lean_ctor_get(v_l_485_, 4);
lean_dec(v_unused_537_);
v_unused_538_ = lean_ctor_get(v_l_485_, 3);
lean_dec(v_unused_538_);
v_unused_539_ = lean_ctor_get(v_l_485_, 2);
lean_dec(v_unused_539_);
v_unused_540_ = lean_ctor_get(v_l_485_, 1);
lean_dec(v_unused_540_);
v_unused_541_ = lean_ctor_get(v_l_485_, 0);
lean_dec(v_unused_541_);
v___x_509_ = v_l_485_;
v_isShared_510_ = v_isSharedCheck_536_;
goto v_resetjp_508_;
}
else
{
lean_dec(v_l_485_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_536_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_526_; 
v___x_511_ = lean_unsigned_to_nat(1u);
v___x_512_ = lean_nat_add(v___x_511_, v_size_481_);
v___x_513_ = lean_nat_add(v___x_512_, v_size_482_);
lean_dec(v_size_482_);
if (lean_obj_tag(v_l_502_) == 0)
{
lean_object* v_size_534_; 
v_size_534_ = lean_ctor_get(v_l_502_, 0);
lean_inc(v_size_534_);
v___y_526_ = v_size_534_;
goto v___jp_525_;
}
else
{
lean_object* v___x_535_; 
v___x_535_ = lean_unsigned_to_nat(0u);
v___y_526_ = v___x_535_;
goto v___jp_525_;
}
v___jp_514_:
{
lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_518_ = lean_nat_add(v___y_515_, v___y_517_);
lean_dec(v___y_517_);
lean_dec(v___y_515_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 4, v_r_486_);
lean_ctor_set(v___x_509_, 3, v_r_503_);
lean_ctor_set(v___x_509_, 2, v_v_484_);
lean_ctor_set(v___x_509_, 1, v_k_483_);
lean_ctor_set(v___x_509_, 0, v___x_518_);
v___x_520_ = v___x_509_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_k_483_);
lean_ctor_set(v_reuseFailAlloc_524_, 2, v_v_484_);
lean_ctor_set(v_reuseFailAlloc_524_, 3, v_r_503_);
lean_ctor_set(v_reuseFailAlloc_524_, 4, v_r_486_);
v___x_520_ = v_reuseFailAlloc_524_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_522_; 
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 4, v___x_520_);
lean_ctor_set(v___x_497_, 3, v___y_516_);
lean_ctor_set(v___x_497_, 2, v_v_501_);
lean_ctor_set(v___x_497_, 1, v_k_500_);
lean_ctor_set(v___x_497_, 0, v___x_513_);
v___x_522_ = v___x_497_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_k_500_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v_v_501_);
lean_ctor_set(v_reuseFailAlloc_523_, 3, v___y_516_);
lean_ctor_set(v_reuseFailAlloc_523_, 4, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
v___jp_525_:
{
lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_527_ = lean_nat_add(v___x_512_, v___y_526_);
lean_dec(v___y_526_);
lean_dec(v___x_512_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v_l_502_);
lean_ctor_set(v___x_476_, 0, v___x_527_);
v___x_529_ = v___x_476_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_533_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_533_, 3, v_l_473_);
lean_ctor_set(v_reuseFailAlloc_533_, 4, v_l_502_);
v___x_529_ = v_reuseFailAlloc_533_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_530_; 
v___x_530_ = lean_nat_add(v___x_511_, v_size_504_);
if (lean_obj_tag(v_r_503_) == 0)
{
lean_object* v_size_531_; 
v_size_531_ = lean_ctor_get(v_r_503_, 0);
lean_inc(v_size_531_);
v___y_515_ = v___x_530_;
v___y_516_ = v___x_529_;
v___y_517_ = v_size_531_;
goto v___jp_514_;
}
else
{
lean_object* v___x_532_; 
v___x_532_ = lean_unsigned_to_nat(0u);
v___y_515_ = v___x_530_;
v___y_516_ = v___x_529_;
v___y_517_ = v___x_532_;
goto v___jp_514_;
}
}
}
}
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_547_; 
lean_del_object(v___x_476_);
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = lean_nat_add(v___x_542_, v_size_481_);
v___x_544_ = lean_nat_add(v___x_543_, v_size_482_);
lean_dec(v_size_482_);
v___x_545_ = lean_nat_add(v___x_543_, v_size_499_);
lean_dec(v___x_543_);
lean_inc_ref(v_l_473_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 4, v_l_485_);
lean_ctor_set(v___x_497_, 3, v_l_473_);
lean_ctor_set(v___x_497_, 2, v_v_472_);
lean_ctor_set(v___x_497_, 1, v_k_471_);
lean_ctor_set(v___x_497_, 0, v___x_545_);
v___x_547_ = v___x_497_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_560_, 3, v_l_473_);
lean_ctor_set(v_reuseFailAlloc_560_, 4, v_l_485_);
v___x_547_ = v_reuseFailAlloc_560_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_isSharedCheck_554_ = !lean_is_exclusive(v_l_473_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; lean_object* v_unused_556_; lean_object* v_unused_557_; lean_object* v_unused_558_; lean_object* v_unused_559_; 
v_unused_555_ = lean_ctor_get(v_l_473_, 4);
lean_dec(v_unused_555_);
v_unused_556_ = lean_ctor_get(v_l_473_, 3);
lean_dec(v_unused_556_);
v_unused_557_ = lean_ctor_get(v_l_473_, 2);
lean_dec(v_unused_557_);
v_unused_558_ = lean_ctor_get(v_l_473_, 1);
lean_dec(v_unused_558_);
v_unused_559_ = lean_ctor_get(v_l_473_, 0);
lean_dec(v_unused_559_);
v___x_549_ = v_l_473_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_dec(v_l_473_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 4, v_r_486_);
lean_ctor_set(v___x_549_, 3, v___x_547_);
lean_ctor_set(v___x_549_, 2, v_v_484_);
lean_ctor_set(v___x_549_, 1, v_k_483_);
lean_ctor_set(v___x_549_, 0, v___x_544_);
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_k_483_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v_v_484_);
lean_ctor_set(v_reuseFailAlloc_553_, 3, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_553_, 4, v_r_486_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec_ref(v_l_485_);
lean_del_object(v___x_497_);
lean_dec(v_v_484_);
lean_dec(v_k_483_);
lean_dec(v_size_482_);
lean_dec_ref(v_l_473_);
lean_del_object(v___x_476_);
lean_dec(v_v_472_);
lean_dec(v_k_471_);
v___x_561_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3);
v___x_562_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v___x_561_);
return v___x_562_;
}
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_del_object(v___x_497_);
lean_dec(v_r_486_);
lean_dec(v_v_484_);
lean_dec(v_k_483_);
lean_dec(v_size_482_);
lean_dec_ref(v_l_473_);
lean_del_object(v___x_476_);
lean_dec(v_v_472_);
lean_dec(v_k_471_);
v___x_563_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4);
v___x_564_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v___x_563_);
return v___x_564_;
}
}
}
}
else
{
lean_object* v_size_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
v_size_571_ = lean_ctor_get(v_l_473_, 0);
v___x_572_ = lean_unsigned_to_nat(1u);
v___x_573_ = lean_nat_add(v___x_572_, v_size_571_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_480_);
lean_ctor_set(v___x_476_, 0, v___x_573_);
v___x_575_ = v___x_476_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_576_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_576_, 3, v_l_473_);
lean_ctor_set(v_reuseFailAlloc_576_, 4, v___x_480_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
else
{
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_l_577_; 
v_l_577_ = lean_ctor_get(v___x_480_, 3);
lean_inc(v_l_577_);
if (lean_obj_tag(v_l_577_) == 0)
{
lean_object* v_r_578_; 
v_r_578_ = lean_ctor_get(v___x_480_, 4);
lean_inc(v_r_578_);
if (lean_obj_tag(v_r_578_) == 0)
{
lean_object* v_size_579_; lean_object* v_k_580_; lean_object* v_v_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_595_; 
v_size_579_ = lean_ctor_get(v___x_480_, 0);
v_k_580_ = lean_ctor_get(v___x_480_, 1);
v_v_581_ = lean_ctor_get(v___x_480_, 2);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; lean_object* v_unused_597_; 
v_unused_596_ = lean_ctor_get(v___x_480_, 4);
lean_dec(v_unused_596_);
v_unused_597_ = lean_ctor_get(v___x_480_, 3);
lean_dec(v_unused_597_);
v___x_583_ = v___x_480_;
v_isShared_584_ = v_isSharedCheck_595_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_v_581_);
lean_inc(v_k_580_);
lean_inc(v_size_579_);
lean_dec(v___x_480_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_595_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v_size_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
v_size_585_ = lean_ctor_get(v_l_577_, 0);
v___x_586_ = lean_unsigned_to_nat(1u);
v___x_587_ = lean_nat_add(v___x_586_, v_size_579_);
lean_dec(v_size_579_);
v___x_588_ = lean_nat_add(v___x_586_, v_size_585_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 4, v_l_577_);
lean_ctor_set(v___x_583_, 3, v_l_473_);
lean_ctor_set(v___x_583_, 2, v_v_472_);
lean_ctor_set(v___x_583_, 1, v_k_471_);
lean_ctor_set(v___x_583_, 0, v___x_588_);
v___x_590_ = v___x_583_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_594_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_594_, 3, v_l_473_);
lean_ctor_set(v_reuseFailAlloc_594_, 4, v_l_577_);
v___x_590_ = v_reuseFailAlloc_594_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_592_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v_r_578_);
lean_ctor_set(v___x_476_, 3, v___x_590_);
lean_ctor_set(v___x_476_, 2, v_v_581_);
lean_ctor_set(v___x_476_, 1, v_k_580_);
lean_ctor_set(v___x_476_, 0, v___x_587_);
v___x_592_ = v___x_476_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_k_580_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v_v_581_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v___x_590_);
lean_ctor_set(v_reuseFailAlloc_593_, 4, v_r_578_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
else
{
lean_object* v_k_598_; lean_object* v_v_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_623_; 
v_k_598_ = lean_ctor_get(v___x_480_, 1);
v_v_599_ = lean_ctor_get(v___x_480_, 2);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_623_ == 0)
{
lean_object* v_unused_624_; lean_object* v_unused_625_; lean_object* v_unused_626_; 
v_unused_624_ = lean_ctor_get(v___x_480_, 4);
lean_dec(v_unused_624_);
v_unused_625_ = lean_ctor_get(v___x_480_, 3);
lean_dec(v_unused_625_);
v_unused_626_ = lean_ctor_get(v___x_480_, 0);
lean_dec(v_unused_626_);
v___x_601_ = v___x_480_;
v_isShared_602_ = v_isSharedCheck_623_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_v_599_);
lean_inc(v_k_598_);
lean_dec(v___x_480_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_623_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v_k_603_; lean_object* v_v_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_619_; 
v_k_603_ = lean_ctor_get(v_l_577_, 1);
v_v_604_ = lean_ctor_get(v_l_577_, 2);
v_isSharedCheck_619_ = !lean_is_exclusive(v_l_577_);
if (v_isSharedCheck_619_ == 0)
{
lean_object* v_unused_620_; lean_object* v_unused_621_; lean_object* v_unused_622_; 
v_unused_620_ = lean_ctor_get(v_l_577_, 4);
lean_dec(v_unused_620_);
v_unused_621_ = lean_ctor_get(v_l_577_, 3);
lean_dec(v_unused_621_);
v_unused_622_ = lean_ctor_get(v_l_577_, 0);
lean_dec(v_unused_622_);
v___x_606_ = v_l_577_;
v_isShared_607_ = v_isSharedCheck_619_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_v_604_);
lean_inc(v_k_603_);
lean_dec(v_l_577_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_619_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_608_ = lean_unsigned_to_nat(3u);
v___x_609_ = lean_unsigned_to_nat(1u);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 4, v_r_578_);
lean_ctor_set(v___x_606_, 3, v_r_578_);
lean_ctor_set(v___x_606_, 2, v_v_472_);
lean_ctor_set(v___x_606_, 1, v_k_471_);
lean_ctor_set(v___x_606_, 0, v___x_609_);
v___x_611_ = v___x_606_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_618_, 3, v_r_578_);
lean_ctor_set(v_reuseFailAlloc_618_, 4, v_r_578_);
v___x_611_ = v_reuseFailAlloc_618_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_613_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 3, v_r_578_);
lean_ctor_set(v___x_601_, 0, v___x_609_);
v___x_613_ = v___x_601_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_k_598_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_v_599_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v_r_578_);
lean_ctor_set(v_reuseFailAlloc_617_, 4, v_r_578_);
v___x_613_ = v_reuseFailAlloc_617_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_615_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_613_);
lean_ctor_set(v___x_476_, 3, v___x_611_);
lean_ctor_set(v___x_476_, 2, v_v_604_);
lean_ctor_set(v___x_476_, 1, v_k_603_);
lean_ctor_set(v___x_476_, 0, v___x_608_);
v___x_615_ = v___x_476_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_k_603_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_v_604_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_627_; 
v_r_627_ = lean_ctor_get(v___x_480_, 4);
lean_inc(v_r_627_);
if (lean_obj_tag(v_r_627_) == 0)
{
lean_object* v_k_628_; lean_object* v_v_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_641_; 
v_k_628_ = lean_ctor_get(v___x_480_, 1);
v_v_629_ = lean_ctor_get(v___x_480_, 2);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; lean_object* v_unused_643_; lean_object* v_unused_644_; 
v_unused_642_ = lean_ctor_get(v___x_480_, 4);
lean_dec(v_unused_642_);
v_unused_643_ = lean_ctor_get(v___x_480_, 3);
lean_dec(v_unused_643_);
v_unused_644_ = lean_ctor_get(v___x_480_, 0);
lean_dec(v_unused_644_);
v___x_631_ = v___x_480_;
v_isShared_632_ = v_isSharedCheck_641_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_v_629_);
lean_inc(v_k_628_);
lean_dec(v___x_480_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_641_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_633_ = lean_unsigned_to_nat(3u);
v___x_634_ = lean_unsigned_to_nat(1u);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 4, v_l_577_);
lean_ctor_set(v___x_631_, 2, v_v_472_);
lean_ctor_set(v___x_631_, 1, v_k_471_);
lean_ctor_set(v___x_631_, 0, v___x_634_);
v___x_636_ = v___x_631_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_640_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_640_, 3, v_l_577_);
lean_ctor_set(v_reuseFailAlloc_640_, 4, v_l_577_);
v___x_636_ = v_reuseFailAlloc_640_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_638_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v_r_627_);
lean_ctor_set(v___x_476_, 3, v___x_636_);
lean_ctor_set(v___x_476_, 2, v_v_629_);
lean_ctor_set(v___x_476_, 1, v_k_628_);
lean_ctor_set(v___x_476_, 0, v___x_633_);
v___x_638_ = v___x_476_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_k_628_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v_v_629_);
lean_ctor_set(v_reuseFailAlloc_639_, 3, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_639_, 4, v_r_627_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
else
{
lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_645_ = lean_unsigned_to_nat(2u);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_480_);
lean_ctor_set(v___x_476_, 3, v_r_627_);
lean_ctor_set(v___x_476_, 0, v___x_645_);
v___x_647_ = v___x_476_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_648_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_648_, 3, v_r_627_);
lean_ctor_set(v_reuseFailAlloc_648_, 4, v___x_480_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
else
{
lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_649_ = lean_unsigned_to_nat(1u);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_480_);
lean_ctor_set(v___x_476_, 3, v___x_480_);
lean_ctor_set(v___x_476_, 0, v___x_649_);
v___x_651_ = v___x_476_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_652_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_652_, 3, v___x_480_);
lean_ctor_set(v_reuseFailAlloc_652_, 4, v___x_480_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
else
{
lean_object* v___x_654_; 
lean_dec(v_v_472_);
lean_dec(v_k_471_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 2, v_v_468_);
lean_ctor_set(v___x_476_, 1, v_k_467_);
v___x_654_ = v___x_476_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_size_470_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_k_467_);
lean_ctor_set(v_reuseFailAlloc_655_, 2, v_v_468_);
lean_ctor_set(v_reuseFailAlloc_655_, 3, v_l_473_);
lean_ctor_set(v_reuseFailAlloc_655_, 4, v_r_474_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
else
{
lean_object* v___x_656_; 
lean_dec(v_size_470_);
v___x_656_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(v_k_467_, v_v_468_, v_l_473_);
if (lean_obj_tag(v_r_474_) == 0)
{
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_size_657_; lean_object* v_size_658_; lean_object* v_k_659_; lean_object* v_v_660_; lean_object* v_l_661_; lean_object* v_r_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v_size_657_ = lean_ctor_get(v_r_474_, 0);
v_size_658_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_size_658_);
v_k_659_ = lean_ctor_get(v___x_656_, 1);
lean_inc(v_k_659_);
v_v_660_ = lean_ctor_get(v___x_656_, 2);
lean_inc(v_v_660_);
v_l_661_ = lean_ctor_get(v___x_656_, 3);
lean_inc(v_l_661_);
v_r_662_ = lean_ctor_get(v___x_656_, 4);
lean_inc(v_r_662_);
v___x_663_ = lean_unsigned_to_nat(3u);
v___x_664_ = lean_nat_mul(v___x_663_, v_size_657_);
v___x_665_ = lean_nat_dec_lt(v___x_664_, v_size_658_);
lean_dec(v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
lean_dec(v_r_662_);
lean_dec(v_l_661_);
lean_dec(v_v_660_);
lean_dec(v_k_659_);
v___x_666_ = lean_unsigned_to_nat(1u);
v___x_667_ = lean_nat_add(v___x_666_, v_size_658_);
lean_dec(v_size_658_);
v___x_668_ = lean_nat_add(v___x_667_, v_size_657_);
lean_dec(v___x_667_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 3, v___x_656_);
lean_ctor_set(v___x_476_, 0, v___x_668_);
v___x_670_ = v___x_476_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_671_, 3, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_671_, 4, v_r_474_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
else
{
lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_743_; 
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_743_ == 0)
{
lean_object* v_unused_744_; lean_object* v_unused_745_; lean_object* v_unused_746_; lean_object* v_unused_747_; lean_object* v_unused_748_; 
v_unused_744_ = lean_ctor_get(v___x_656_, 4);
lean_dec(v_unused_744_);
v_unused_745_ = lean_ctor_get(v___x_656_, 3);
lean_dec(v_unused_745_);
v_unused_746_ = lean_ctor_get(v___x_656_, 2);
lean_dec(v_unused_746_);
v_unused_747_ = lean_ctor_get(v___x_656_, 1);
lean_dec(v_unused_747_);
v_unused_748_ = lean_ctor_get(v___x_656_, 0);
lean_dec(v_unused_748_);
v___x_673_ = v___x_656_;
v_isShared_674_ = v_isSharedCheck_743_;
goto v_resetjp_672_;
}
else
{
lean_dec(v___x_656_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_743_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
if (lean_obj_tag(v_l_661_) == 0)
{
if (lean_obj_tag(v_r_662_) == 0)
{
lean_object* v_size_675_; lean_object* v_size_676_; lean_object* v_k_677_; lean_object* v_v_678_; lean_object* v_l_679_; lean_object* v_r_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v_size_675_ = lean_ctor_get(v_l_661_, 0);
v_size_676_ = lean_ctor_get(v_r_662_, 0);
v_k_677_ = lean_ctor_get(v_r_662_, 1);
v_v_678_ = lean_ctor_get(v_r_662_, 2);
v_l_679_ = lean_ctor_get(v_r_662_, 3);
v_r_680_ = lean_ctor_get(v_r_662_, 4);
v___x_681_ = lean_unsigned_to_nat(2u);
v___x_682_ = lean_nat_mul(v___x_681_, v_size_675_);
v___x_683_ = lean_nat_dec_lt(v_size_676_, v___x_682_);
lean_dec(v___x_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_713_; 
lean_inc(v_r_680_);
lean_inc(v_l_679_);
lean_inc(v_v_678_);
lean_inc(v_k_677_);
v_isSharedCheck_713_ = !lean_is_exclusive(v_r_662_);
if (v_isSharedCheck_713_ == 0)
{
lean_object* v_unused_714_; lean_object* v_unused_715_; lean_object* v_unused_716_; lean_object* v_unused_717_; lean_object* v_unused_718_; 
v_unused_714_ = lean_ctor_get(v_r_662_, 4);
lean_dec(v_unused_714_);
v_unused_715_ = lean_ctor_get(v_r_662_, 3);
lean_dec(v_unused_715_);
v_unused_716_ = lean_ctor_get(v_r_662_, 2);
lean_dec(v_unused_716_);
v_unused_717_ = lean_ctor_get(v_r_662_, 1);
lean_dec(v_unused_717_);
v_unused_718_ = lean_ctor_get(v_r_662_, 0);
lean_dec(v_unused_718_);
v___x_685_ = v_r_662_;
v_isShared_686_ = v_isSharedCheck_713_;
goto v_resetjp_684_;
}
else
{
lean_dec(v_r_662_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_713_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___x_701_; lean_object* v___y_703_; 
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = lean_nat_add(v___x_687_, v_size_658_);
lean_dec(v_size_658_);
v___x_689_ = lean_nat_add(v___x_688_, v_size_657_);
lean_dec(v___x_688_);
v___x_701_ = lean_nat_add(v___x_687_, v_size_675_);
if (lean_obj_tag(v_l_679_) == 0)
{
lean_object* v_size_711_; 
v_size_711_ = lean_ctor_get(v_l_679_, 0);
lean_inc(v_size_711_);
v___y_703_ = v_size_711_;
goto v___jp_702_;
}
else
{
lean_object* v___x_712_; 
v___x_712_ = lean_unsigned_to_nat(0u);
v___y_703_ = v___x_712_;
goto v___jp_702_;
}
v___jp_690_:
{
lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_694_ = lean_nat_add(v___y_691_, v___y_693_);
lean_dec(v___y_693_);
lean_dec(v___y_691_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 4, v_r_474_);
lean_ctor_set(v___x_685_, 3, v_r_680_);
lean_ctor_set(v___x_685_, 2, v_v_472_);
lean_ctor_set(v___x_685_, 1, v_k_471_);
lean_ctor_set(v___x_685_, 0, v___x_694_);
v___x_696_ = v___x_685_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v_r_680_);
lean_ctor_set(v_reuseFailAlloc_700_, 4, v_r_474_);
v___x_696_ = v_reuseFailAlloc_700_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_698_; 
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 4, v___x_696_);
lean_ctor_set(v___x_673_, 3, v___y_692_);
lean_ctor_set(v___x_673_, 2, v_v_678_);
lean_ctor_set(v___x_673_, 1, v_k_677_);
lean_ctor_set(v___x_673_, 0, v___x_689_);
v___x_698_ = v___x_673_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_k_677_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v_v_678_);
lean_ctor_set(v_reuseFailAlloc_699_, 3, v___y_692_);
lean_ctor_set(v_reuseFailAlloc_699_, 4, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
v___jp_702_:
{
lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_704_ = lean_nat_add(v___x_701_, v___y_703_);
lean_dec(v___y_703_);
lean_dec(v___x_701_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v_l_679_);
lean_ctor_set(v___x_476_, 3, v_l_661_);
lean_ctor_set(v___x_476_, 2, v_v_660_);
lean_ctor_set(v___x_476_, 1, v_k_659_);
lean_ctor_set(v___x_476_, 0, v___x_704_);
v___x_706_ = v___x_476_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_710_, 3, v_l_661_);
lean_ctor_set(v_reuseFailAlloc_710_, 4, v_l_679_);
v___x_706_ = v_reuseFailAlloc_710_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_707_; 
v___x_707_ = lean_nat_add(v___x_687_, v_size_657_);
if (lean_obj_tag(v_r_680_) == 0)
{
lean_object* v_size_708_; 
v_size_708_ = lean_ctor_get(v_r_680_, 0);
lean_inc(v_size_708_);
v___y_691_ = v___x_707_;
v___y_692_ = v___x_706_;
v___y_693_ = v_size_708_;
goto v___jp_690_;
}
else
{
lean_object* v___x_709_; 
v___x_709_ = lean_unsigned_to_nat(0u);
v___y_691_ = v___x_707_;
v___y_692_ = v___x_706_;
v___y_693_ = v___x_709_;
goto v___jp_690_;
}
}
}
}
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
lean_del_object(v___x_476_);
v___x_719_ = lean_unsigned_to_nat(1u);
v___x_720_ = lean_nat_add(v___x_719_, v_size_658_);
lean_dec(v_size_658_);
v___x_721_ = lean_nat_add(v___x_720_, v_size_657_);
lean_dec(v___x_720_);
v___x_722_ = lean_nat_add(v___x_719_, v_size_657_);
v___x_723_ = lean_nat_add(v___x_722_, v_size_676_);
lean_dec(v___x_722_);
lean_inc_ref(v_r_474_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 4, v_r_474_);
lean_ctor_set(v___x_673_, 3, v_r_662_);
lean_ctor_set(v___x_673_, 2, v_v_472_);
lean_ctor_set(v___x_673_, 1, v_k_471_);
lean_ctor_set(v___x_673_, 0, v___x_723_);
v___x_725_ = v___x_673_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_738_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_738_, 3, v_r_662_);
lean_ctor_set(v_reuseFailAlloc_738_, 4, v_r_474_);
v___x_725_ = v_reuseFailAlloc_738_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
v_isSharedCheck_732_ = !lean_is_exclusive(v_r_474_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; lean_object* v_unused_734_; lean_object* v_unused_735_; lean_object* v_unused_736_; lean_object* v_unused_737_; 
v_unused_733_ = lean_ctor_get(v_r_474_, 4);
lean_dec(v_unused_733_);
v_unused_734_ = lean_ctor_get(v_r_474_, 3);
lean_dec(v_unused_734_);
v_unused_735_ = lean_ctor_get(v_r_474_, 2);
lean_dec(v_unused_735_);
v_unused_736_ = lean_ctor_get(v_r_474_, 1);
lean_dec(v_unused_736_);
v_unused_737_ = lean_ctor_get(v_r_474_, 0);
lean_dec(v_unused_737_);
v___x_727_ = v_r_474_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_dec(v_r_474_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 4, v___x_725_);
lean_ctor_set(v___x_727_, 3, v_l_661_);
lean_ctor_set(v___x_727_, 2, v_v_660_);
lean_ctor_set(v___x_727_, 1, v_k_659_);
lean_ctor_set(v___x_727_, 0, v___x_721_);
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_731_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_731_, 3, v_l_661_);
lean_ctor_set(v_reuseFailAlloc_731_, 4, v___x_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; 
lean_dec_ref(v_l_661_);
lean_del_object(v___x_673_);
lean_dec(v_v_660_);
lean_dec(v_k_659_);
lean_dec(v_size_658_);
lean_dec_ref(v_r_474_);
lean_del_object(v___x_476_);
lean_dec(v_v_472_);
lean_dec(v_k_471_);
v___x_739_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7);
v___x_740_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v___x_739_);
return v___x_740_;
}
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; 
lean_del_object(v___x_673_);
lean_dec(v_r_662_);
lean_dec(v_v_660_);
lean_dec(v_k_659_);
lean_dec(v_size_658_);
lean_dec_ref(v_r_474_);
lean_del_object(v___x_476_);
lean_dec(v_v_472_);
lean_dec(v_k_471_);
v___x_741_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8);
v___x_742_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v___x_741_);
return v___x_742_;
}
}
}
}
else
{
lean_object* v_size_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
v_size_749_ = lean_ctor_get(v_r_474_, 0);
v___x_750_ = lean_unsigned_to_nat(1u);
v___x_751_ = lean_nat_add(v___x_750_, v_size_749_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 3, v___x_656_);
lean_ctor_set(v___x_476_, 0, v___x_751_);
v___x_753_ = v___x_476_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_754_, 3, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_754_, 4, v_r_474_);
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
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_l_755_; 
v_l_755_ = lean_ctor_get(v___x_656_, 3);
lean_inc(v_l_755_);
if (lean_obj_tag(v_l_755_) == 0)
{
lean_object* v_r_756_; 
v_r_756_ = lean_ctor_get(v___x_656_, 4);
lean_inc(v_r_756_);
if (lean_obj_tag(v_r_756_) == 0)
{
lean_object* v_size_757_; lean_object* v_k_758_; lean_object* v_v_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_773_; 
v_size_757_ = lean_ctor_get(v___x_656_, 0);
v_k_758_ = lean_ctor_get(v___x_656_, 1);
v_v_759_ = lean_ctor_get(v___x_656_, 2);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; lean_object* v_unused_775_; 
v_unused_774_ = lean_ctor_get(v___x_656_, 4);
lean_dec(v_unused_774_);
v_unused_775_ = lean_ctor_get(v___x_656_, 3);
lean_dec(v_unused_775_);
v___x_761_ = v___x_656_;
v_isShared_762_ = v_isSharedCheck_773_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_v_759_);
lean_inc(v_k_758_);
lean_inc(v_size_757_);
lean_dec(v___x_656_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_773_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_size_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
v_size_763_ = lean_ctor_get(v_r_756_, 0);
v___x_764_ = lean_unsigned_to_nat(1u);
v___x_765_ = lean_nat_add(v___x_764_, v_size_757_);
lean_dec(v_size_757_);
v___x_766_ = lean_nat_add(v___x_764_, v_size_763_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 4, v_r_474_);
lean_ctor_set(v___x_761_, 3, v_r_756_);
lean_ctor_set(v___x_761_, 2, v_v_472_);
lean_ctor_set(v___x_761_, 1, v_k_471_);
lean_ctor_set(v___x_761_, 0, v___x_766_);
v___x_768_ = v___x_761_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v_r_756_);
lean_ctor_set(v_reuseFailAlloc_772_, 4, v_r_474_);
v___x_768_ = v_reuseFailAlloc_772_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_770_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_768_);
lean_ctor_set(v___x_476_, 3, v_l_755_);
lean_ctor_set(v___x_476_, 2, v_v_759_);
lean_ctor_set(v___x_476_, 1, v_k_758_);
lean_ctor_set(v___x_476_, 0, v___x_765_);
v___x_770_ = v___x_476_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_k_758_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v_v_759_);
lean_ctor_set(v_reuseFailAlloc_771_, 3, v_l_755_);
lean_ctor_set(v_reuseFailAlloc_771_, 4, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
else
{
lean_object* v_k_776_; lean_object* v_v_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_789_; 
v_k_776_ = lean_ctor_get(v___x_656_, 1);
v_v_777_ = lean_ctor_get(v___x_656_, 2);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_789_ == 0)
{
lean_object* v_unused_790_; lean_object* v_unused_791_; lean_object* v_unused_792_; 
v_unused_790_ = lean_ctor_get(v___x_656_, 4);
lean_dec(v_unused_790_);
v_unused_791_ = lean_ctor_get(v___x_656_, 3);
lean_dec(v_unused_791_);
v_unused_792_ = lean_ctor_get(v___x_656_, 0);
lean_dec(v_unused_792_);
v___x_779_ = v___x_656_;
v_isShared_780_ = v_isSharedCheck_789_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_v_777_);
lean_inc(v_k_776_);
lean_dec(v___x_656_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_789_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_781_ = lean_unsigned_to_nat(3u);
v___x_782_ = lean_unsigned_to_nat(1u);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 3, v_r_756_);
lean_ctor_set(v___x_779_, 2, v_v_472_);
lean_ctor_set(v___x_779_, 1, v_k_471_);
lean_ctor_set(v___x_779_, 0, v___x_782_);
v___x_784_ = v___x_779_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_788_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_788_, 3, v_r_756_);
lean_ctor_set(v_reuseFailAlloc_788_, 4, v_r_756_);
v___x_784_ = v_reuseFailAlloc_788_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_786_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_784_);
lean_ctor_set(v___x_476_, 3, v_l_755_);
lean_ctor_set(v___x_476_, 2, v_v_777_);
lean_ctor_set(v___x_476_, 1, v_k_776_);
lean_ctor_set(v___x_476_, 0, v___x_781_);
v___x_786_ = v___x_476_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_k_776_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v_v_777_);
lean_ctor_set(v_reuseFailAlloc_787_, 3, v_l_755_);
lean_ctor_set(v_reuseFailAlloc_787_, 4, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
else
{
lean_object* v_r_793_; 
v_r_793_ = lean_ctor_get(v___x_656_, 4);
lean_inc(v_r_793_);
if (lean_obj_tag(v_r_793_) == 0)
{
lean_object* v_k_794_; lean_object* v_v_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_819_; 
v_k_794_ = lean_ctor_get(v___x_656_, 1);
v_v_795_ = lean_ctor_get(v___x_656_, 2);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; lean_object* v_unused_821_; lean_object* v_unused_822_; 
v_unused_820_ = lean_ctor_get(v___x_656_, 4);
lean_dec(v_unused_820_);
v_unused_821_ = lean_ctor_get(v___x_656_, 3);
lean_dec(v_unused_821_);
v_unused_822_ = lean_ctor_get(v___x_656_, 0);
lean_dec(v_unused_822_);
v___x_797_ = v___x_656_;
v_isShared_798_ = v_isSharedCheck_819_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_v_795_);
lean_inc(v_k_794_);
lean_dec(v___x_656_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_819_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v_k_799_; lean_object* v_v_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_815_; 
v_k_799_ = lean_ctor_get(v_r_793_, 1);
v_v_800_ = lean_ctor_get(v_r_793_, 2);
v_isSharedCheck_815_ = !lean_is_exclusive(v_r_793_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; lean_object* v_unused_817_; lean_object* v_unused_818_; 
v_unused_816_ = lean_ctor_get(v_r_793_, 4);
lean_dec(v_unused_816_);
v_unused_817_ = lean_ctor_get(v_r_793_, 3);
lean_dec(v_unused_817_);
v_unused_818_ = lean_ctor_get(v_r_793_, 0);
lean_dec(v_unused_818_);
v___x_802_ = v_r_793_;
v_isShared_803_ = v_isSharedCheck_815_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_v_800_);
lean_inc(v_k_799_);
lean_dec(v_r_793_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_815_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_804_ = lean_unsigned_to_nat(3u);
v___x_805_ = lean_unsigned_to_nat(1u);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 4, v_l_755_);
lean_ctor_set(v___x_802_, 3, v_l_755_);
lean_ctor_set(v___x_802_, 2, v_v_795_);
lean_ctor_set(v___x_802_, 1, v_k_794_);
lean_ctor_set(v___x_802_, 0, v___x_805_);
v___x_807_ = v___x_802_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_k_794_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v_v_795_);
lean_ctor_set(v_reuseFailAlloc_814_, 3, v_l_755_);
lean_ctor_set(v_reuseFailAlloc_814_, 4, v_l_755_);
v___x_807_ = v_reuseFailAlloc_814_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_809_; 
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 4, v_l_755_);
lean_ctor_set(v___x_797_, 2, v_v_472_);
lean_ctor_set(v___x_797_, 1, v_k_471_);
lean_ctor_set(v___x_797_, 0, v___x_805_);
v___x_809_ = v___x_797_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_813_, 3, v_l_755_);
lean_ctor_set(v_reuseFailAlloc_813_, 4, v_l_755_);
v___x_809_ = v_reuseFailAlloc_813_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_811_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_809_);
lean_ctor_set(v___x_476_, 3, v___x_807_);
lean_ctor_set(v___x_476_, 2, v_v_800_);
lean_ctor_set(v___x_476_, 1, v_k_799_);
lean_ctor_set(v___x_476_, 0, v___x_804_);
v___x_811_ = v___x_476_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_804_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_k_799_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v_v_800_);
lean_ctor_set(v_reuseFailAlloc_812_, 3, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_812_, 4, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
}
else
{
lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_823_ = lean_unsigned_to_nat(2u);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v_r_793_);
lean_ctor_set(v___x_476_, 3, v___x_656_);
lean_ctor_set(v___x_476_, 0, v___x_823_);
v___x_825_ = v___x_476_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_826_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_826_, 3, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_826_, 4, v_r_793_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
else
{
lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_827_ = lean_unsigned_to_nat(1u);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_656_);
lean_ctor_set(v___x_476_, 3, v___x_656_);
lean_ctor_set(v___x_476_, 0, v___x_827_);
v___x_829_ = v___x_476_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_830_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_830_, 3, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_830_, 4, v___x_656_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
}
}
else
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = lean_unsigned_to_nat(1u);
v___x_833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v_k_467_);
lean_ctor_set(v___x_833_, 2, v_v_468_);
lean_ctor_set(v___x_833_, 3, v_t_469_);
lean_ctor_set(v___x_833_, 4, v_t_469_);
return v___x_833_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1_spec__5(lean_object* v_init_834_, lean_object* v_x_835_){
_start:
{
if (lean_obj_tag(v_x_835_) == 0)
{
lean_object* v_k_836_; lean_object* v_v_837_; lean_object* v_l_838_; lean_object* v_r_839_; lean_object* v___x_840_; uint8_t v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v_k_836_ = lean_ctor_get(v_x_835_, 1);
lean_inc(v_k_836_);
v_v_837_ = lean_ctor_get(v_x_835_, 2);
lean_inc(v_v_837_);
v_l_838_ = lean_ctor_get(v_x_835_, 3);
lean_inc(v_l_838_);
v_r_839_ = lean_ctor_get(v_x_835_, 4);
lean_inc(v_r_839_);
lean_dec_ref(v_x_835_);
v___x_840_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1_spec__5(v_init_834_, v_l_838_);
v___x_841_ = 1;
v___x_842_ = l_Lean_Name_toString(v_k_836_, v___x_841_);
v___x_843_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_843_, 0, v_v_837_);
v___x_844_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(v___x_842_, v___x_843_, v___x_840_);
v_init_834_ = v___x_844_;
v_x_835_ = v_r_839_;
goto _start;
}
else
{
return v_init_834_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0(lean_object* v_m_846_){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_847_ = lean_box(1);
v___x_848_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1_spec__5(v___x_847_, v_m_846_);
v___x_849_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson(lean_object* v_x_850_){
_start:
{
if (lean_obj_tag(v_x_850_) == 0)
{
lean_object* v_name_851_; lean_object* v_opts_852_; uint8_t v_inherited_853_; lean_object* v_dir_854_; lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_name_851_ = lean_ctor_get(v_x_850_, 0);
lean_inc(v_name_851_);
v_opts_852_ = lean_ctor_get(v_x_850_, 1);
lean_inc(v_opts_852_);
v_inherited_853_ = lean_ctor_get_uint8(v_x_850_, sizeof(void*)*3);
v_dir_854_ = lean_ctor_get(v_x_850_, 2);
lean_inc_ref(v_dir_854_);
lean_dec_ref(v_x_850_);
v___x_855_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2));
v___x_856_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_857_ = 1;
v___x_858_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_851_, v___x_857_);
v___x_859_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_856_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__8));
v___x_862_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0(v_opts_852_);
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10));
v___x_865_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_865_, 0, v_inherited_853_);
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_864_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22));
v___x_868_ = l_Lake_mkRelPathString(v_dir_854_);
v___x_869_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_867_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = lean_box(0);
v___x_872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_870_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_866_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_863_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_860_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = l_Lean_Json_mkObj(v___x_875_);
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_855_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
lean_ctor_set(v___x_878_, 1, v___x_871_);
v___x_879_ = l_Lean_Json_mkObj(v___x_878_);
return v___x_879_;
}
else
{
lean_object* v_name_880_; lean_object* v_opts_881_; uint8_t v_inherited_882_; lean_object* v_url_883_; lean_object* v_rev_884_; lean_object* v_inputRev_x3f_885_; lean_object* v_subDir_x3f_886_; lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v_name_880_ = lean_ctor_get(v_x_850_, 0);
lean_inc(v_name_880_);
v_opts_881_ = lean_ctor_get(v_x_850_, 1);
lean_inc(v_opts_881_);
v_inherited_882_ = lean_ctor_get_uint8(v_x_850_, sizeof(void*)*6);
v_url_883_ = lean_ctor_get(v_x_850_, 2);
lean_inc_ref(v_url_883_);
v_rev_884_ = lean_ctor_get(v_x_850_, 3);
lean_inc_ref(v_rev_884_);
v_inputRev_x3f_885_ = lean_ctor_get(v_x_850_, 4);
lean_inc(v_inputRev_x3f_885_);
v_subDir_x3f_886_ = lean_ctor_get(v_x_850_, 5);
lean_inc(v_subDir_x3f_886_);
lean_dec_ref(v_x_850_);
v___x_887_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3));
v___x_888_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_889_ = 1;
v___x_890_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_880_, v___x_889_);
v___x_891_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
v___x_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_888_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__8));
v___x_894_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0(v_opts_881_);
v___x_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10));
v___x_897_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_897_, 0, v_inherited_882_);
v___x_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12));
v___x_900_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_900_, 0, v_url_883_);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14));
v___x_903_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_903_, 0, v_rev_884_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__16));
v___x_906_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__1(v_inputRev_x3f_885_);
v___x_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_905_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__18));
v___x_909_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_subDir_x3f_886_);
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_box(0);
v___x_912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_910_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_907_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_904_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_901_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_898_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_895_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_892_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = l_Lean_Json_mkObj(v___x_918_);
v___x_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_887_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set(v___x_921_, 1, v___x_911_);
v___x_922_ = l_Lean_Json_mkObj(v___x_921_);
return v___x_922_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_923_, lean_object* v_msg_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v_msg_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0(lean_object* v_00_u03b2_926_, lean_object* v_k_927_, lean_object* v_v_928_, lean_object* v_t_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(v_k_927_, v_v_928_, v_t_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1(lean_object* v_init_931_, lean_object* v_t_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1_spec__5(v_init_931_, v_t_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorIdx(lean_object* v_x_943_){
_start:
{
if (lean_obj_tag(v_x_943_) == 0)
{
lean_object* v___x_944_; 
v___x_944_ = lean_unsigned_to_nat(0u);
return v___x_944_;
}
else
{
lean_object* v___x_945_; 
v___x_945_ = lean_unsigned_to_nat(1u);
return v___x_945_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorIdx___boxed(lean_object* v_x_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lake_PackageEntrySrc_ctorIdx(v_x_946_);
lean_dec_ref(v_x_946_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorElim___redArg(lean_object* v_t_948_, lean_object* v_k_949_){
_start:
{
if (lean_obj_tag(v_t_948_) == 0)
{
lean_object* v_dir_950_; lean_object* v___x_951_; 
v_dir_950_ = lean_ctor_get(v_t_948_, 0);
lean_inc_ref(v_dir_950_);
lean_dec_ref(v_t_948_);
v___x_951_ = lean_apply_1(v_k_949_, v_dir_950_);
return v___x_951_;
}
else
{
lean_object* v_url_952_; lean_object* v_rev_953_; lean_object* v_inputRev_x3f_954_; lean_object* v_subDir_x3f_955_; lean_object* v___x_956_; 
v_url_952_ = lean_ctor_get(v_t_948_, 0);
lean_inc_ref(v_url_952_);
v_rev_953_ = lean_ctor_get(v_t_948_, 1);
lean_inc_ref(v_rev_953_);
v_inputRev_x3f_954_ = lean_ctor_get(v_t_948_, 2);
lean_inc(v_inputRev_x3f_954_);
v_subDir_x3f_955_ = lean_ctor_get(v_t_948_, 3);
lean_inc(v_subDir_x3f_955_);
lean_dec_ref(v_t_948_);
v___x_956_ = lean_apply_4(v_k_949_, v_url_952_, v_rev_953_, v_inputRev_x3f_954_, v_subDir_x3f_955_);
return v___x_956_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorElim(lean_object* v_motive_957_, lean_object* v_ctorIdx_958_, lean_object* v_t_959_, lean_object* v_h_960_, lean_object* v_k_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_959_, v_k_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorElim___boxed(lean_object* v_motive_963_, lean_object* v_ctorIdx_964_, lean_object* v_t_965_, lean_object* v_h_966_, lean_object* v_k_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lake_PackageEntrySrc_ctorElim(v_motive_963_, v_ctorIdx_964_, v_t_965_, v_h_966_, v_k_967_);
lean_dec(v_ctorIdx_964_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_path_elim___redArg(lean_object* v_t_969_, lean_object* v_path_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_969_, v_path_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_path_elim(lean_object* v_motive_972_, lean_object* v_t_973_, lean_object* v_h_974_, lean_object* v_path_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_973_, v_path_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_git_elim___redArg(lean_object* v_t_977_, lean_object* v_git_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_977_, v_git_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_git_elim(lean_object* v_motive_980_, lean_object* v_t_981_, lean_object* v_h_982_, lean_object* v_git_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_981_, v_git_983_);
return v___x_984_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntry_default___closed__0(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_989_ = ((lean_object*)(l_Lake_instInhabitedPackageEntrySrc_default));
v___x_990_ = lean_box(0);
v___x_991_ = l_Lake_defaultConfigFile;
v___x_992_ = 0;
v___x_993_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_994_ = lean_box(0);
v___x_995_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v___x_993_);
lean_ctor_set(v___x_995_, 2, v___x_991_);
lean_ctor_set(v___x_995_, 3, v___x_990_);
lean_ctor_set(v___x_995_, 4, v___x_989_);
lean_ctor_set_uint8(v___x_995_, sizeof(void*)*5, v___x_992_);
return v___x_995_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntry_default(void){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = lean_obj_once(&l_Lake_instInhabitedPackageEntry_default___closed__0, &l_Lake_instInhabitedPackageEntry_default___closed__0_once, _init_l_Lake_instInhabitedPackageEntry_default___closed__0);
return v___x_996_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntry(void){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lake_instInhabitedPackageEntry_default;
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_prettyName(lean_object* v_entry_998_){
_start:
{
lean_object* v_name_999_; uint8_t v___x_1000_; lean_object* v___x_1001_; 
v_name_999_ = lean_ctor_get(v_entry_998_, 0);
lean_inc(v_name_999_);
lean_dec_ref(v_entry_998_);
v___x_1000_ = 0;
v___x_1001_ = l_Lean_Name_toString(v_name_999_, v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_toJson(lean_object* v_entry_1018_){
_start:
{
lean_object* v_name_1019_; lean_object* v_scope_1020_; uint8_t v_inherited_1021_; lean_object* v_configFile_1022_; lean_object* v_manifestFile_x3f_1023_; lean_object* v_src_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v_fields_1048_; 
v_name_1019_ = lean_ctor_get(v_entry_1018_, 0);
lean_inc(v_name_1019_);
v_scope_1020_ = lean_ctor_get(v_entry_1018_, 1);
lean_inc_ref(v_scope_1020_);
v_inherited_1021_ = lean_ctor_get_uint8(v_entry_1018_, sizeof(void*)*5);
v_configFile_1022_ = lean_ctor_get(v_entry_1018_, 2);
lean_inc_ref(v_configFile_1022_);
v_manifestFile_x3f_1023_ = lean_ctor_get(v_entry_1018_, 3);
lean_inc(v_manifestFile_x3f_1023_);
v_src_1024_ = lean_ctor_get(v_entry_1018_, 4);
lean_inc_ref(v_src_1024_);
lean_dec_ref(v_entry_1018_);
v___x_1025_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_1026_ = 1;
v___x_1027_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1019_, v___x_1026_);
v___x_1028_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1025_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__0));
v___x_1031_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1031_, 0, v_scope_1020_);
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__1));
v___x_1034_ = l_Lake_mkRelPathString(v_configFile_1022_);
v___x_1035_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1033_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__2));
v___x_1038_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_manifestFile_x3f_1023_);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10));
v___x_1041_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1041_, 0, v_inherited_1021_);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_box(0);
v___x_1044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1042_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1039_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1036_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1032_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v_fields_1048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_fields_1048_, 0, v___x_1029_);
lean_ctor_set(v_fields_1048_, 1, v___x_1047_);
if (lean_obj_tag(v_src_1024_) == 0)
{
lean_object* v_dir_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1064_; 
v_dir_1049_ = lean_ctor_get(v_src_1024_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_src_1024_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1051_ = v_src_1024_;
v_isShared_1052_ = v_isSharedCheck_1064_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_dir_1049_);
lean_dec(v_src_1024_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1064_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1053_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__5));
v___x_1054_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22));
v___x_1055_ = l_Lake_mkRelPathString(v_dir_1049_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set_tag(v___x_1051_, 3);
lean_ctor_set(v___x_1051_, 0, v___x_1055_);
v___x_1057_ = v___x_1051_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1054_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
lean_ctor_set(v___x_1059_, 1, v___x_1043_);
v___x_1060_ = l_List_appendTR___redArg(v_fields_1048_, v___x_1059_);
v___x_1061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1053_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = l_Lean_Json_mkObj(v___x_1061_);
return v___x_1062_;
}
}
}
else
{
lean_object* v_url_1065_; lean_object* v_rev_1066_; lean_object* v_inputRev_x3f_1067_; lean_object* v_subDir_x3f_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v_url_1065_ = lean_ctor_get(v_src_1024_, 0);
lean_inc_ref(v_url_1065_);
v_rev_1066_ = lean_ctor_get(v_src_1024_, 1);
lean_inc_ref(v_rev_1066_);
v_inputRev_x3f_1067_ = lean_ctor_get(v_src_1024_, 2);
lean_inc(v_inputRev_x3f_1067_);
v_subDir_x3f_1068_ = lean_ctor_get(v_src_1024_, 3);
lean_inc(v_subDir_x3f_1068_);
lean_dec_ref(v_src_1024_);
v___x_1069_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__7));
v___x_1070_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12));
v___x_1071_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1071_, 0, v_url_1065_);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14));
v___x_1074_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1074_, 0, v_rev_1066_);
v___x_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__8));
v___x_1077_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__1(v_inputRev_x3f_1067_);
v___x_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1076_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__9));
v___x_1080_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_subDir_x3f_1068_);
v___x_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1079_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set(v___x_1082_, 1, v___x_1043_);
v___x_1083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1078_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1075_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1072_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = l_List_appendTR___redArg(v_fields_1048_, v___x_1085_);
v___x_1087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1069_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = l_Lean_Json_mkObj(v___x_1087_);
return v___x_1088_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0(lean_object* v_x_1092_){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0));
v___x_1094_ = lean_string_append(v___x_1093_, v_x_1092_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0___boxed(lean_object* v_x_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_x_1095_);
lean_dec_ref(v_x_1095_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f(lean_object* v_json_1117_){
_start:
{
lean_object* v_a_1119_; lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_Json_getObj_x3f(v_json_1117_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1131_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1125_ = v___x_1122_;
v_isShared_1126_ = v_isSharedCheck_1131_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1122_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1131_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1127_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_a_1123_);
lean_dec(v_a_1123_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 0, v___x_1127_);
v___x_1129_ = v___x_1125_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
else
{
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
v_a_1132_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1122_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1122_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
lean_ctor_set_tag(v___x_1134_, 0);
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1362_; 
v_a_1140_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1142_ = v___x_1122_;
v_isShared_1143_ = v_isSharedCheck_1362_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1122_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1362_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_1145_ = l_Lake_JsonObject_getJson_x3f(v_a_1140_, v___x_1144_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v___x_1146_; 
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v___x_1146_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__0));
v_a_1119_ = v___x_1146_;
goto v___jp_1118_;
}
else
{
lean_object* v_val_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1361_; 
v_val_1147_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1149_ = v___x_1145_;
v_isShared_1150_ = v_isSharedCheck_1361_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_val_1147_);
lean_dec(v___x_1145_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1361_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_Name_fromJson_x3f(v_val_1147_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_a_1152_);
lean_dec_ref(v___x_1151_);
v___x_1153_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__1));
v___x_1154_ = lean_string_append(v___x_1153_, v_a_1152_);
lean_dec(v_a_1152_);
v_a_1119_ = v___x_1154_;
goto v___jp_1118_;
}
else
{
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1155_; 
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v_a_1155_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_a_1155_);
lean_dec_ref(v___x_1151_);
v_a_1119_ = v_a_1155_;
goto v___jp_1118_;
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1360_; 
v_a_1156_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1158_ = v___x_1151_;
v_isShared_1159_ = v_isSharedCheck_1360_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1151_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1360_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v_a_1161_; uint8_t v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v_a_1177_; uint8_t v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v_a_1193_; lean_object* v___y_1196_; uint8_t v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v_a_1202_; uint8_t v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v_a_1218_; uint8_t v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; uint8_t v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v_a_1283_; uint8_t v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v_a_1300_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__0));
v___x_1337_ = l_Lake_JsonObject_getJson_x3f(v_a_1140_, v___x_1336_);
if (lean_obj_tag(v___x_1337_) == 0)
{
goto v___jp_1334_;
}
else
{
lean_object* v_val_1338_; lean_object* v___x_1339_; 
v_val_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_val_1338_);
lean_dec_ref(v___x_1337_);
v___x_1339_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(v_val_1338_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1349_; 
lean_del_object(v___x_1158_);
lean_dec(v_a_1156_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1342_ = v___x_1339_;
v_isShared_1343_ = v_isSharedCheck_1349_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1339_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1349_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1347_; 
v___x_1344_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__19));
v___x_1345_ = lean_string_append(v___x_1344_, v_a_1340_);
lean_dec(v_a_1340_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1345_);
v___x_1347_ = v___x_1342_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
else
{
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_del_object(v___x_1158_);
lean_dec(v_a_1156_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v_a_1350_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1339_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1339_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
lean_ctor_set_tag(v___x_1352_, 0);
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
else
{
lean_object* v_a_1358_; 
v_a_1358_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1358_);
lean_dec_ref(v___x_1339_);
if (lean_obj_tag(v_a_1358_) == 0)
{
goto v___jp_1334_;
}
else
{
lean_object* v_val_1359_; 
v_val_1359_ = lean_ctor_get(v_a_1358_, 0);
lean_inc(v_val_1359_);
lean_dec_ref(v_a_1358_);
v_a_1300_ = v_val_1359_;
goto v___jp_1299_;
}
}
}
}
v___jp_1160_:
{
lean_object* v___x_1162_; uint8_t v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1162_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__2));
v___x_1163_ = 1;
v___x_1164_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_1156_, v___x_1163_);
v___x_1165_ = lean_string_append(v___x_1162_, v___x_1164_);
lean_dec_ref(v___x_1164_);
v___x_1166_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__3));
v___x_1167_ = lean_string_append(v___x_1165_, v___x_1166_);
v___x_1168_ = lean_string_append(v___x_1167_, v_a_1161_);
lean_dec_ref(v_a_1161_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set_tag(v___x_1158_, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1168_);
v___x_1170_ = v___x_1158_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
v___jp_1172_:
{
lean_object* v___x_1179_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___y_1175_);
v___x_1179_ = v___x_1149_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___y_1175_);
v___x_1179_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1180_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1180_, 0, v_a_1156_);
lean_ctor_set(v___x_1180_, 1, v___y_1174_);
lean_ctor_set(v___x_1180_, 2, v___y_1176_);
lean_ctor_set(v___x_1180_, 3, v___x_1179_);
lean_ctor_set(v___x_1180_, 4, v_a_1177_);
lean_ctor_set_uint8(v___x_1180_, sizeof(void*)*5, v___y_1173_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1180_);
v___x_1182_ = v___x_1142_;
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
}
v___jp_1185_:
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1194_, 0, v___y_1187_);
lean_ctor_set(v___x_1194_, 1, v___y_1191_);
lean_ctor_set(v___x_1194_, 2, v___y_1189_);
lean_ctor_set(v___x_1194_, 3, v_a_1193_);
v___y_1173_ = v___y_1186_;
v___y_1174_ = v___y_1188_;
v___y_1175_ = v___y_1190_;
v___y_1176_ = v___y_1192_;
v_a_1177_ = v___x_1194_;
goto v___jp_1172_;
}
v___jp_1195_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__9));
v___x_1204_ = l_Lake_JsonObject_getJson_x3f(v_a_1140_, v___x_1203_);
lean_dec(v_a_1140_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v___x_1205_; 
lean_del_object(v___x_1158_);
v___x_1205_ = lean_box(0);
v___y_1186_ = v___y_1197_;
v___y_1187_ = v___y_1196_;
v___y_1188_ = v___y_1198_;
v___y_1189_ = v_a_1202_;
v___y_1190_ = v___y_1199_;
v___y_1191_ = v___y_1200_;
v___y_1192_ = v___y_1201_;
v_a_1193_ = v___x_1205_;
goto v___jp_1185_;
}
else
{
lean_object* v_val_1206_; lean_object* v___x_1207_; 
v_val_1206_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_val_1206_);
lean_dec_ref(v___x_1204_);
v___x_1207_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1206_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
lean_dec(v_a_1202_);
lean_dec_ref(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec_ref(v___y_1196_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1208_);
lean_dec_ref(v___x_1207_);
v___x_1209_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__4));
v___x_1210_ = lean_string_append(v___x_1209_, v_a_1208_);
lean_dec(v_a_1208_);
v_a_1161_ = v___x_1210_;
goto v___jp_1160_;
}
else
{
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1211_; 
lean_dec(v_a_1202_);
lean_dec_ref(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec_ref(v___y_1196_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
v_a_1211_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1211_);
lean_dec_ref(v___x_1207_);
v_a_1161_ = v_a_1211_;
goto v___jp_1160_;
}
else
{
lean_object* v_a_1212_; 
lean_del_object(v___x_1158_);
v_a_1212_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1212_);
lean_dec_ref(v___x_1207_);
v___y_1186_ = v___y_1197_;
v___y_1187_ = v___y_1196_;
v___y_1188_ = v___y_1198_;
v___y_1189_ = v_a_1202_;
v___y_1190_ = v___y_1199_;
v___y_1191_ = v___y_1200_;
v___y_1192_ = v___y_1201_;
v_a_1193_ = v_a_1212_;
goto v___jp_1185_;
}
}
}
}
v___jp_1213_:
{
lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1219_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2));
v___x_1220_ = lean_string_dec_eq(v___y_1216_, v___x_1219_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1221_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3));
v___x_1222_ = lean_string_dec_eq(v___y_1216_, v___x_1221_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
lean_dec_ref(v_a_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v___y_1215_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v___x_1223_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__5));
v___x_1224_ = lean_string_append(v___x_1223_, v___y_1216_);
lean_dec_ref(v___y_1216_);
v___x_1225_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1226_ = lean_string_append(v___x_1224_, v___x_1225_);
v_a_1161_ = v___x_1226_;
goto v___jp_1160_;
}
else
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
lean_dec_ref(v___y_1216_);
v___x_1227_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12));
v___x_1228_ = l_Lake_JsonObject_getJson_x3f(v_a_1140_, v___x_1227_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v___x_1229_; 
lean_dec_ref(v_a_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v___y_1215_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v___x_1229_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__6));
v_a_1161_ = v___x_1229_;
goto v___jp_1160_;
}
else
{
lean_object* v_val_1230_; lean_object* v___x_1231_; 
v_val_1230_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_val_1230_);
lean_dec_ref(v___x_1228_);
v___x_1231_ = l_Lean_Json_getStr_x3f(v_val_1230_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_dec_ref(v_a_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v___y_1215_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
lean_dec_ref(v___x_1231_);
v___x_1233_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__7));
v___x_1234_ = lean_string_append(v___x_1233_, v_a_1232_);
lean_dec(v_a_1232_);
v_a_1161_ = v___x_1234_;
goto v___jp_1160_;
}
else
{
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1235_; 
lean_dec_ref(v_a_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v___y_1215_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v_a_1235_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1235_);
lean_dec_ref(v___x_1231_);
v_a_1161_ = v_a_1235_;
goto v___jp_1160_;
}
else
{
lean_object* v_a_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v_a_1236_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1236_);
lean_dec_ref(v___x_1231_);
v___x_1237_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14));
v___x_1238_ = l_Lake_JsonObject_getJson_x3f(v_a_1140_, v___x_1237_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v___x_1239_; 
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v___y_1215_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v___x_1239_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__8));
v_a_1161_ = v___x_1239_;
goto v___jp_1160_;
}
else
{
lean_object* v_val_1240_; lean_object* v___x_1241_; 
v_val_1240_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_val_1240_);
lean_dec_ref(v___x_1238_);
v___x_1241_ = l_Lean_Json_getStr_x3f(v_val_1240_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v___y_1215_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref(v___x_1241_);
v___x_1243_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__9));
v___x_1244_ = lean_string_append(v___x_1243_, v_a_1242_);
lean_dec(v_a_1242_);
v_a_1161_ = v___x_1244_;
goto v___jp_1160_;
}
else
{
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1245_; 
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v___y_1215_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v_a_1245_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1245_);
lean_dec_ref(v___x_1241_);
v_a_1161_ = v_a_1245_;
goto v___jp_1160_;
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v_a_1246_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1246_);
lean_dec_ref(v___x_1241_);
v___x_1247_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__8));
v___x_1248_ = l_Lake_JsonObject_getJson_x3f(v_a_1140_, v___x_1247_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_box(0);
v___y_1196_ = v_a_1236_;
v___y_1197_ = v___y_1214_;
v___y_1198_ = v___y_1215_;
v___y_1199_ = v_a_1218_;
v___y_1200_ = v_a_1246_;
v___y_1201_ = v___y_1217_;
v_a_1202_ = v___x_1249_;
goto v___jp_1195_;
}
else
{
lean_object* v_val_1250_; lean_object* v___x_1251_; 
v_val_1250_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_val_1250_);
lean_dec_ref(v___x_1248_);
v___x_1251_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(v_val_1250_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec(v_a_1246_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v___y_1215_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref(v___x_1251_);
v___x_1253_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__10));
v___x_1254_ = lean_string_append(v___x_1253_, v_a_1252_);
lean_dec(v_a_1252_);
v_a_1161_ = v___x_1254_;
goto v___jp_1160_;
}
else
{
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1255_; 
lean_dec(v_a_1246_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v___y_1215_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v_a_1255_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1255_);
lean_dec_ref(v___x_1251_);
v_a_1161_ = v_a_1255_;
goto v___jp_1160_;
}
else
{
lean_object* v_a_1256_; 
v_a_1256_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1256_);
lean_dec_ref(v___x_1251_);
v___y_1196_ = v_a_1236_;
v___y_1197_ = v___y_1214_;
v___y_1198_ = v___y_1215_;
v___y_1199_ = v_a_1218_;
v___y_1200_ = v_a_1246_;
v___y_1201_ = v___y_1217_;
v_a_1202_ = v_a_1256_;
goto v___jp_1195_;
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
else
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
lean_dec_ref(v___y_1216_);
v___x_1257_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22));
v___x_1258_ = l_Lake_JsonObject_getJson_x3f(v_a_1140_, v___x_1257_);
lean_dec(v_a_1140_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v___x_1259_; 
lean_dec_ref(v_a_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v___y_1215_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
v___x_1259_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__11));
v_a_1161_ = v___x_1259_;
goto v___jp_1160_;
}
else
{
lean_object* v_val_1260_; lean_object* v___x_1261_; 
v_val_1260_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_val_1260_);
lean_dec_ref(v___x_1258_);
v___x_1261_ = l_Lean_Json_getStr_x3f(v_val_1260_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_dec_ref(v_a_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v___y_1215_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref(v___x_1261_);
v___x_1263_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__12));
v___x_1264_ = lean_string_append(v___x_1263_, v_a_1262_);
lean_dec(v_a_1262_);
v_a_1161_ = v___x_1264_;
goto v___jp_1160_;
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_del_object(v___x_1158_);
v_a_1265_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1261_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1261_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
lean_ctor_set_tag(v___x_1267_, 0);
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
v___y_1173_ = v___y_1214_;
v___y_1174_ = v___y_1215_;
v___y_1175_ = v_a_1218_;
v___y_1176_ = v___y_1217_;
v_a_1177_ = v___x_1270_;
goto v___jp_1172_;
}
}
}
}
}
}
v___jp_1273_:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lake_defaultManifestFile;
v___y_1214_ = v___y_1274_;
v___y_1215_ = v___y_1275_;
v___y_1216_ = v___y_1276_;
v___y_1217_ = v___y_1277_;
v_a_1218_ = v___x_1278_;
goto v___jp_1213_;
}
v___jp_1279_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__2));
v___x_1285_ = l_Lake_JsonObject_getJson_x3f(v_a_1140_, v___x_1284_);
if (lean_obj_tag(v___x_1285_) == 0)
{
v___y_1274_ = v___y_1280_;
v___y_1275_ = v___y_1281_;
v___y_1276_ = v___y_1282_;
v___y_1277_ = v_a_1283_;
goto v___jp_1273_;
}
else
{
lean_object* v_val_1286_; lean_object* v___x_1287_; 
v_val_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_val_1286_);
lean_dec_ref(v___x_1285_);
v___x_1287_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1286_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
lean_dec_ref(v_a_1283_);
lean_dec_ref(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref(v___x_1287_);
v___x_1289_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__13));
v___x_1290_ = lean_string_append(v___x_1289_, v_a_1288_);
lean_dec(v_a_1288_);
v_a_1161_ = v___x_1290_;
goto v___jp_1160_;
}
else
{
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1291_; 
lean_dec_ref(v_a_1283_);
lean_dec_ref(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v_a_1291_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1291_);
lean_dec_ref(v___x_1287_);
v_a_1161_ = v_a_1291_;
goto v___jp_1160_;
}
else
{
lean_object* v_a_1292_; 
v_a_1292_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1292_);
lean_dec_ref(v___x_1287_);
if (lean_obj_tag(v_a_1292_) == 0)
{
v___y_1274_ = v___y_1280_;
v___y_1275_ = v___y_1281_;
v___y_1276_ = v___y_1282_;
v___y_1277_ = v_a_1283_;
goto v___jp_1273_;
}
else
{
lean_object* v_val_1293_; 
v_val_1293_ = lean_ctor_get(v_a_1292_, 0);
lean_inc(v_val_1293_);
lean_dec_ref(v_a_1292_);
v___y_1214_ = v___y_1280_;
v___y_1215_ = v___y_1281_;
v___y_1216_ = v___y_1282_;
v___y_1217_ = v_a_1283_;
v_a_1218_ = v_val_1293_;
goto v___jp_1213_;
}
}
}
}
}
v___jp_1294_:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Lake_defaultConfigFile;
v___y_1280_ = v___y_1295_;
v___y_1281_ = v___y_1296_;
v___y_1282_ = v___y_1297_;
v_a_1283_ = v___x_1298_;
goto v___jp_1279_;
}
v___jp_1299_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__3));
v___x_1302_ = l_Lake_JsonObject_getJson_x3f(v_a_1140_, v___x_1301_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v___x_1303_; 
lean_dec_ref(v_a_1300_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v___x_1303_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__14));
v_a_1161_ = v___x_1303_;
goto v___jp_1160_;
}
else
{
lean_object* v_val_1304_; lean_object* v___x_1305_; 
v_val_1304_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_val_1304_);
lean_dec_ref(v___x_1302_);
v___x_1305_ = l_Lean_Json_getStr_x3f(v_val_1304_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
lean_dec_ref(v_a_1300_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1306_);
lean_dec_ref(v___x_1305_);
v___x_1307_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__15));
v___x_1308_ = lean_string_append(v___x_1307_, v_a_1306_);
lean_dec(v_a_1306_);
v_a_1161_ = v___x_1308_;
goto v___jp_1160_;
}
else
{
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1309_; 
lean_dec_ref(v_a_1300_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v_a_1309_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1309_);
lean_dec_ref(v___x_1305_);
v_a_1161_ = v_a_1309_;
goto v___jp_1160_;
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v_a_1310_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1310_);
lean_dec_ref(v___x_1305_);
v___x_1311_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10));
v___x_1312_ = l_Lake_JsonObject_getJson_x3f(v_a_1140_, v___x_1311_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v___x_1313_; 
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1300_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v___x_1313_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__16));
v_a_1161_ = v___x_1313_;
goto v___jp_1160_;
}
else
{
lean_object* v_val_1314_; lean_object* v___x_1315_; 
v_val_1314_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_val_1314_);
lean_dec_ref(v___x_1312_);
v___x_1315_ = l_Lean_Json_getBool_x3f(v_val_1314_);
lean_dec(v_val_1314_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1300_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
lean_dec_ref(v___x_1315_);
v___x_1317_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__17));
v___x_1318_ = lean_string_append(v___x_1317_, v_a_1316_);
lean_dec(v_a_1316_);
v_a_1161_ = v___x_1318_;
goto v___jp_1160_;
}
else
{
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1319_; 
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1300_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v_a_1319_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1319_);
lean_dec_ref(v___x_1315_);
v_a_1161_ = v_a_1319_;
goto v___jp_1160_;
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v_a_1320_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1320_);
lean_dec_ref(v___x_1315_);
v___x_1321_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__1));
v___x_1322_ = l_Lake_JsonObject_getJson_x3f(v_a_1140_, v___x_1321_);
if (lean_obj_tag(v___x_1322_) == 0)
{
uint8_t v___x_1323_; 
v___x_1323_ = lean_unbox(v_a_1320_);
lean_dec(v_a_1320_);
v___y_1295_ = v___x_1323_;
v___y_1296_ = v_a_1300_;
v___y_1297_ = v_a_1310_;
goto v___jp_1294_;
}
else
{
lean_object* v_val_1324_; lean_object* v___x_1325_; 
v_val_1324_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_val_1324_);
lean_dec_ref(v___x_1322_);
v___x_1325_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1324_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
lean_dec(v_a_1320_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1300_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref(v___x_1325_);
v___x_1327_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__18));
v___x_1328_ = lean_string_append(v___x_1327_, v_a_1326_);
lean_dec(v_a_1326_);
v_a_1161_ = v___x_1328_;
goto v___jp_1160_;
}
else
{
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1329_; 
lean_dec(v_a_1320_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1300_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1140_);
v_a_1329_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1329_);
lean_dec_ref(v___x_1325_);
v_a_1161_ = v_a_1329_;
goto v___jp_1160_;
}
else
{
lean_object* v_a_1330_; 
v_a_1330_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1330_);
lean_dec_ref(v___x_1325_);
if (lean_obj_tag(v_a_1330_) == 0)
{
uint8_t v___x_1331_; 
v___x_1331_ = lean_unbox(v_a_1320_);
lean_dec(v_a_1320_);
v___y_1295_ = v___x_1331_;
v___y_1296_ = v_a_1300_;
v___y_1297_ = v_a_1310_;
goto v___jp_1294_;
}
else
{
lean_object* v_val_1332_; uint8_t v___x_1333_; 
v_val_1332_ = lean_ctor_get(v_a_1330_, 0);
lean_inc(v_val_1332_);
lean_dec_ref(v_a_1330_);
v___x_1333_ = lean_unbox(v_a_1320_);
lean_dec(v_a_1320_);
v___y_1280_ = v___x_1333_;
v___y_1281_ = v_a_1300_;
v___y_1282_ = v_a_1310_;
v_a_1283_ = v_val_1332_;
goto v___jp_1279_;
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
v___jp_1334_:
{
lean_object* v___x_1335_; 
v___x_1335_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v_a_1300_ = v___x_1335_;
goto v___jp_1299_;
}
}
}
}
}
}
}
}
}
v___jp_1118_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_a_1119_);
lean_dec_ref(v_a_1119_);
v___x_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
return v___x_1121_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setInherited(lean_object* v_entry_1365_){
_start:
{
lean_object* v_name_1366_; lean_object* v_scope_1367_; lean_object* v_configFile_1368_; lean_object* v_manifestFile_x3f_1369_; lean_object* v_src_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1378_; 
v_name_1366_ = lean_ctor_get(v_entry_1365_, 0);
v_scope_1367_ = lean_ctor_get(v_entry_1365_, 1);
v_configFile_1368_ = lean_ctor_get(v_entry_1365_, 2);
v_manifestFile_x3f_1369_ = lean_ctor_get(v_entry_1365_, 3);
v_src_1370_ = lean_ctor_get(v_entry_1365_, 4);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_entry_1365_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1372_ = v_entry_1365_;
v_isShared_1373_ = v_isSharedCheck_1378_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_src_1370_);
lean_inc(v_manifestFile_x3f_1369_);
lean_inc(v_configFile_1368_);
lean_inc(v_scope_1367_);
lean_inc(v_name_1366_);
lean_dec(v_entry_1365_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1378_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
uint8_t v___x_1374_; lean_object* v___x_1376_; 
v___x_1374_ = 1;
if (v_isShared_1373_ == 0)
{
v___x_1376_ = v___x_1372_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_name_1366_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_scope_1367_);
lean_ctor_set(v_reuseFailAlloc_1377_, 2, v_configFile_1368_);
lean_ctor_set(v_reuseFailAlloc_1377_, 3, v_manifestFile_x3f_1369_);
lean_ctor_set(v_reuseFailAlloc_1377_, 4, v_src_1370_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_ctor_set_uint8(v___x_1376_, sizeof(void*)*5, v___x_1374_);
return v___x_1376_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setConfigFile(lean_object* v_path_1379_, lean_object* v_entry_1380_){
_start:
{
lean_object* v_name_1381_; lean_object* v_scope_1382_; uint8_t v_inherited_1383_; lean_object* v_manifestFile_x3f_1384_; lean_object* v_src_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
v_name_1381_ = lean_ctor_get(v_entry_1380_, 0);
v_scope_1382_ = lean_ctor_get(v_entry_1380_, 1);
v_inherited_1383_ = lean_ctor_get_uint8(v_entry_1380_, sizeof(void*)*5);
v_manifestFile_x3f_1384_ = lean_ctor_get(v_entry_1380_, 3);
v_src_1385_ = lean_ctor_get(v_entry_1380_, 4);
v_isSharedCheck_1392_ = !lean_is_exclusive(v_entry_1380_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; 
v_unused_1393_ = lean_ctor_get(v_entry_1380_, 2);
lean_dec(v_unused_1393_);
v___x_1387_ = v_entry_1380_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_src_1385_);
lean_inc(v_manifestFile_x3f_1384_);
lean_inc(v_scope_1382_);
lean_inc(v_name_1381_);
lean_dec(v_entry_1380_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 2, v_path_1379_);
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_name_1381_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_scope_1382_);
lean_ctor_set(v_reuseFailAlloc_1391_, 2, v_path_1379_);
lean_ctor_set(v_reuseFailAlloc_1391_, 3, v_manifestFile_x3f_1384_);
lean_ctor_set(v_reuseFailAlloc_1391_, 4, v_src_1385_);
lean_ctor_set_uint8(v_reuseFailAlloc_1391_, sizeof(void*)*5, v_inherited_1383_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setManifestFile(lean_object* v_path_x3f_1394_, lean_object* v_entry_1395_){
_start:
{
lean_object* v_name_1396_; lean_object* v_scope_1397_; uint8_t v_inherited_1398_; lean_object* v_configFile_1399_; lean_object* v_src_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
v_name_1396_ = lean_ctor_get(v_entry_1395_, 0);
v_scope_1397_ = lean_ctor_get(v_entry_1395_, 1);
v_inherited_1398_ = lean_ctor_get_uint8(v_entry_1395_, sizeof(void*)*5);
v_configFile_1399_ = lean_ctor_get(v_entry_1395_, 2);
v_src_1400_ = lean_ctor_get(v_entry_1395_, 4);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_entry_1395_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; 
v_unused_1408_ = lean_ctor_get(v_entry_1395_, 3);
lean_dec(v_unused_1408_);
v___x_1402_ = v_entry_1395_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_src_1400_);
lean_inc(v_configFile_1399_);
lean_inc(v_scope_1397_);
lean_inc(v_name_1396_);
lean_dec(v_entry_1395_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 3, v_path_x3f_1394_);
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_name_1396_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_scope_1397_);
lean_ctor_set(v_reuseFailAlloc_1406_, 2, v_configFile_1399_);
lean_ctor_set(v_reuseFailAlloc_1406_, 3, v_path_x3f_1394_);
lean_ctor_set(v_reuseFailAlloc_1406_, 4, v_src_1400_);
lean_ctor_set_uint8(v_reuseFailAlloc_1406_, sizeof(void*)*5, v_inherited_1398_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_inDirectory(lean_object* v_pkgDir_1409_, lean_object* v_entry_1410_){
_start:
{
lean_object* v_src_1411_; 
v_src_1411_ = lean_ctor_get(v_entry_1410_, 4);
lean_inc_ref(v_src_1411_);
if (lean_obj_tag(v_src_1411_) == 0)
{
lean_object* v_name_1412_; lean_object* v_scope_1413_; uint8_t v_inherited_1414_; lean_object* v_configFile_1415_; lean_object* v_manifestFile_x3f_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1432_; 
v_name_1412_ = lean_ctor_get(v_entry_1410_, 0);
v_scope_1413_ = lean_ctor_get(v_entry_1410_, 1);
v_inherited_1414_ = lean_ctor_get_uint8(v_entry_1410_, sizeof(void*)*5);
v_configFile_1415_ = lean_ctor_get(v_entry_1410_, 2);
v_manifestFile_x3f_1416_ = lean_ctor_get(v_entry_1410_, 3);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_entry_1410_);
if (v_isSharedCheck_1432_ == 0)
{
lean_object* v_unused_1433_; 
v_unused_1433_ = lean_ctor_get(v_entry_1410_, 4);
lean_dec(v_unused_1433_);
v___x_1418_ = v_entry_1410_;
v_isShared_1419_ = v_isSharedCheck_1432_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_manifestFile_x3f_1416_);
lean_inc(v_configFile_1415_);
lean_inc(v_scope_1413_);
lean_inc(v_name_1412_);
lean_dec(v_entry_1410_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1432_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v_dir_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1431_; 
v_dir_1420_ = lean_ctor_get(v_src_1411_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_src_1411_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1422_ = v_src_1411_;
v_isShared_1423_ = v_isSharedCheck_1431_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_dir_1420_);
lean_dec(v_src_1411_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1431_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1424_ = l_Lake_joinRelative(v_pkgDir_1409_, v_dir_1420_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v___x_1424_);
v___x_1426_ = v___x_1422_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1428_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 4, v___x_1426_);
v___x_1428_ = v___x_1418_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_name_1412_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_scope_1413_);
lean_ctor_set(v_reuseFailAlloc_1429_, 2, v_configFile_1415_);
lean_ctor_set(v_reuseFailAlloc_1429_, 3, v_manifestFile_x3f_1416_);
lean_ctor_set(v_reuseFailAlloc_1429_, 4, v___x_1426_);
lean_ctor_set_uint8(v_reuseFailAlloc_1429_, sizeof(void*)*5, v_inherited_1414_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
}
else
{
lean_dec_ref(v_src_1411_);
lean_dec_ref(v_pkgDir_1409_);
return v_entry_1410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(lean_object* v_x_1434_){
_start:
{
if (lean_obj_tag(v_x_1434_) == 0)
{
lean_object* v_name_1435_; uint8_t v_inherited_1436_; lean_object* v_dir_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v_name_1435_ = lean_ctor_get(v_x_1434_, 0);
v_inherited_1436_ = lean_ctor_get_uint8(v_x_1434_, sizeof(void*)*3);
v_dir_1437_ = lean_ctor_get(v_x_1434_, 2);
v___x_1438_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_1439_ = l_Lake_defaultConfigFile;
v___x_1440_ = lean_box(0);
lean_inc_ref(v_dir_1437_);
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v_dir_1437_);
lean_inc(v_name_1435_);
v___x_1442_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1442_, 0, v_name_1435_);
lean_ctor_set(v___x_1442_, 1, v___x_1438_);
lean_ctor_set(v___x_1442_, 2, v___x_1439_);
lean_ctor_set(v___x_1442_, 3, v___x_1440_);
lean_ctor_set(v___x_1442_, 4, v___x_1441_);
lean_ctor_set_uint8(v___x_1442_, sizeof(void*)*5, v_inherited_1436_);
return v___x_1442_;
}
else
{
lean_object* v_name_1443_; uint8_t v_inherited_1444_; lean_object* v_url_1445_; lean_object* v_rev_1446_; lean_object* v_inputRev_x3f_1447_; lean_object* v_subDir_x3f_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v_name_1443_ = lean_ctor_get(v_x_1434_, 0);
v_inherited_1444_ = lean_ctor_get_uint8(v_x_1434_, sizeof(void*)*6);
v_url_1445_ = lean_ctor_get(v_x_1434_, 2);
v_rev_1446_ = lean_ctor_get(v_x_1434_, 3);
v_inputRev_x3f_1447_ = lean_ctor_get(v_x_1434_, 4);
v_subDir_x3f_1448_ = lean_ctor_get(v_x_1434_, 5);
v___x_1449_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_1450_ = l_Lake_defaultConfigFile;
v___x_1451_ = lean_box(0);
lean_inc(v_subDir_x3f_1448_);
lean_inc(v_inputRev_x3f_1447_);
lean_inc_ref(v_rev_1446_);
lean_inc_ref(v_url_1445_);
v___x_1452_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1452_, 0, v_url_1445_);
lean_ctor_set(v___x_1452_, 1, v_rev_1446_);
lean_ctor_set(v___x_1452_, 2, v_inputRev_x3f_1447_);
lean_ctor_set(v___x_1452_, 3, v_subDir_x3f_1448_);
lean_inc(v_name_1443_);
v___x_1453_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1453_, 0, v_name_1443_);
lean_ctor_set(v___x_1453_, 1, v___x_1449_);
lean_ctor_set(v___x_1453_, 2, v___x_1450_);
lean_ctor_set(v___x_1453_, 3, v___x_1451_);
lean_ctor_set(v___x_1453_, 4, v___x_1452_);
lean_ctor_set_uint8(v___x_1453_, sizeof(void*)*5, v_inherited_1444_);
return v___x_1453_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6___boxed(lean_object* v_x_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(v_x_1454_);
lean_dec_ref(v_x_1454_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_addPackage(lean_object* v_entry_1456_, lean_object* v_self_1457_){
_start:
{
lean_object* v_name_1458_; lean_object* v_lakeDir_1459_; uint8_t v_fixedToolchain_1460_; lean_object* v_packagesDir_x3f_1461_; lean_object* v_packages_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1470_; 
v_name_1458_ = lean_ctor_get(v_self_1457_, 0);
v_lakeDir_1459_ = lean_ctor_get(v_self_1457_, 1);
v_fixedToolchain_1460_ = lean_ctor_get_uint8(v_self_1457_, sizeof(void*)*4);
v_packagesDir_x3f_1461_ = lean_ctor_get(v_self_1457_, 2);
v_packages_1462_ = lean_ctor_get(v_self_1457_, 3);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_self_1457_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1464_ = v_self_1457_;
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_packages_1462_);
lean_inc(v_packagesDir_x3f_1461_);
lean_inc(v_lakeDir_1459_);
lean_inc(v_name_1458_);
lean_dec(v_self_1457_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1466_ = lean_array_push(v_packages_1462_, v_entry_1456_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 3, v___x_1466_);
v___x_1468_ = v___x_1464_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_name_1458_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_lakeDir_1459_);
lean_ctor_set(v_reuseFailAlloc_1469_, 2, v_packagesDir_x3f_1461_);
lean_ctor_set(v_reuseFailAlloc_1469_, 3, v___x_1466_);
lean_ctor_set_uint8(v_reuseFailAlloc_1469_, sizeof(void*)*4, v_fixedToolchain_1460_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(size_t v_sz_1471_, size_t v_i_1472_, lean_object* v_bs_1473_){
_start:
{
uint8_t v___x_1474_; 
v___x_1474_ = lean_usize_dec_lt(v_i_1472_, v_sz_1471_);
if (v___x_1474_ == 0)
{
return v_bs_1473_;
}
else
{
lean_object* v_v_1475_; lean_object* v___x_1476_; lean_object* v_bs_x27_1477_; lean_object* v___x_1478_; size_t v___x_1479_; size_t v___x_1480_; lean_object* v___x_1481_; 
v_v_1475_ = lean_array_uget(v_bs_1473_, v_i_1472_);
v___x_1476_ = lean_unsigned_to_nat(0u);
v_bs_x27_1477_ = lean_array_uset(v_bs_1473_, v_i_1472_, v___x_1476_);
v___x_1478_ = l_Lake_PackageEntry_toJson(v_v_1475_);
v___x_1479_ = ((size_t)1ULL);
v___x_1480_ = lean_usize_add(v_i_1472_, v___x_1479_);
v___x_1481_ = lean_array_uset(v_bs_x27_1477_, v_i_1472_, v___x_1478_);
v_i_1472_ = v___x_1480_;
v_bs_1473_ = v___x_1481_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1483_, lean_object* v_i_1484_, lean_object* v_bs_1485_){
_start:
{
size_t v_sz_boxed_1486_; size_t v_i_boxed_1487_; lean_object* v_res_1488_; 
v_sz_boxed_1486_ = lean_unbox_usize(v_sz_1483_);
lean_dec(v_sz_1483_);
v_i_boxed_1487_ = lean_unbox_usize(v_i_1484_);
lean_dec(v_i_1484_);
v_res_1488_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(v_sz_boxed_1486_, v_i_boxed_1487_, v_bs_1485_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_Manifest_toJson_spec__0(lean_object* v_a_1489_){
_start:
{
size_t v_sz_1490_; size_t v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v_sz_1490_ = lean_array_size(v_a_1489_);
v___x_1491_ = ((size_t)0ULL);
v___x_1492_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(v_sz_1490_, v___x_1491_, v_a_1489_);
v___x_1493_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
return v___x_1493_;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__1(void){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = ((lean_object*)(l_Lake_Manifest_version___closed__2));
v___x_1496_ = l_Lake_StdVer_toString(v___x_1495_);
return v___x_1496_;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__2(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__1, &l_Lake_Manifest_toJson___closed__1_once, _init_l_Lake_Manifest_toJson___closed__1);
v___x_1498_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
return v___x_1498_;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__3(void){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1499_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__2, &l_Lake_Manifest_toJson___closed__2_once, _init_l_Lake_Manifest_toJson___closed__2);
v___x_1500_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__0));
v___x_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
lean_ctor_set(v___x_1501_, 1, v___x_1499_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_toJson(lean_object* v_self_1506_){
_start:
{
lean_object* v_name_1507_; lean_object* v_lakeDir_1508_; uint8_t v_fixedToolchain_1509_; lean_object* v_packagesDir_x3f_1510_; lean_object* v_packages_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; uint8_t v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v_name_1507_ = lean_ctor_get(v_self_1506_, 0);
lean_inc(v_name_1507_);
v_lakeDir_1508_ = lean_ctor_get(v_self_1506_, 1);
lean_inc_ref(v_lakeDir_1508_);
v_fixedToolchain_1509_ = lean_ctor_get_uint8(v_self_1506_, sizeof(void*)*4);
v_packagesDir_x3f_1510_ = lean_ctor_get(v_self_1506_, 2);
lean_inc(v_packagesDir_x3f_1510_);
v_packages_1511_ = lean_ctor_get(v_self_1506_, 3);
lean_inc_ref(v_packages_1511_);
lean_dec_ref(v_self_1506_);
v___x_1512_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__3, &l_Lake_Manifest_toJson___closed__3_once, _init_l_Lake_Manifest_toJson___closed__3);
v___x_1513_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__4));
v___x_1514_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1514_, 0, v_fixedToolchain_1509_);
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1513_);
lean_ctor_set(v___x_1515_, 1, v___x_1514_);
v___x_1516_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_1517_ = 1;
v___x_1518_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1507_, v___x_1517_);
v___x_1519_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
v___x_1520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1516_);
lean_ctor_set(v___x_1520_, 1, v___x_1519_);
v___x_1521_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__5));
v___x_1522_ = l_Lake_mkRelPathString(v_lakeDir_1508_);
v___x_1523_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
v___x_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1521_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
v___x_1525_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__6));
v___x_1526_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_packagesDir_x3f_1510_);
v___x_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1525_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
v___x_1528_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__7));
v___x_1529_ = l_Array_toJson___at___00Lake_Manifest_toJson_spec__0(v_packages_1511_);
v___x_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
v___x_1531_ = lean_box(0);
v___x_1532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1530_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1527_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1524_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v___x_1535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1520_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
v___x_1536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1515_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1512_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = l_Lean_Json_mkObj(v___x_1537_);
return v___x_1538_;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6(void){
_start:
{
lean_object* v_natZero_1549_; lean_object* v_intZero_1550_; 
v_natZero_1549_ = lean_unsigned_to_nat(0u);
v_intZero_1550_ = lean_nat_to_int(v_natZero_1549_);
return v_intZero_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(lean_object* v_obj_1556_){
_start:
{
lean_object* v___y_1558_; lean_object* v_ver_1566_; lean_object* v_major_1567_; lean_object* v_ver_1584_; lean_object* v_a_1593_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__0));
v___x_1620_ = l_Lake_JsonObject_getJson_x3f(v_obj_1556_, v___x_1619_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8));
v___x_1622_ = l_Lake_JsonObject_getJson_x3f(v_obj_1556_, v___x_1621_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v___x_1623_; 
v___x_1623_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__10));
return v___x_1623_;
}
else
{
lean_object* v_val_1624_; 
v_val_1624_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_val_1624_);
lean_dec_ref(v___x_1622_);
v_a_1593_ = v_val_1624_;
goto v___jp_1592_;
}
}
else
{
lean_object* v_val_1625_; 
v_val_1625_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_val_1625_);
lean_dec_ref(v___x_1620_);
v_a_1593_ = v_val_1625_;
goto v___jp_1592_;
}
v___jp_1557_:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1559_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__0));
v___x_1560_ = l_Lake_SemVerCore_toString(v___y_1558_);
v___x_1561_ = lean_string_append(v___x_1559_, v___x_1560_);
lean_dec_ref(v___x_1560_);
v___x_1562_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1563_ = lean_string_append(v___x_1561_, v___x_1562_);
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
return v___x_1564_;
}
v___jp_1565_:
{
lean_object* v___x_1568_; uint8_t v___x_1569_; 
v___x_1568_ = lean_unsigned_to_nat(1u);
v___x_1569_ = lean_nat_dec_lt(v___x_1568_, v_major_1567_);
lean_dec(v_major_1567_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1570_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__1));
v___x_1571_ = l_Lake_instOrdSemVerCore_ord(v_ver_1566_, v___x_1570_);
if (v___x_1571_ == 0)
{
v___y_1558_ = v_ver_1566_;
goto v___jp_1557_;
}
else
{
if (v___x_1569_ == 0)
{
lean_object* v___x_1572_; 
v___x_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1572_, 0, v_ver_1566_);
return v___x_1572_;
}
else
{
v___y_1558_ = v_ver_1566_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1573_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__2));
v___x_1574_ = l_Lake_SemVerCore_toString(v_ver_1566_);
v___x_1575_ = lean_string_append(v___x_1573_, v___x_1574_);
lean_dec_ref(v___x_1574_);
v___x_1576_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__3));
v___x_1577_ = lean_string_append(v___x_1575_, v___x_1576_);
v___x_1578_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__1, &l_Lake_Manifest_toJson___closed__1_once, _init_l_Lake_Manifest_toJson___closed__1);
v___x_1579_ = lean_string_append(v___x_1577_, v___x_1578_);
v___x_1580_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4));
v___x_1581_ = lean_string_append(v___x_1579_, v___x_1580_);
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
return v___x_1582_;
}
}
v___jp_1583_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1585_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__5));
v___x_1586_ = lean_unsigned_to_nat(80u);
v___x_1587_ = l_Lean_Json_pretty(v_ver_1584_, v___x_1586_);
v___x_1588_ = lean_string_append(v___x_1585_, v___x_1587_);
lean_dec_ref(v___x_1587_);
v___x_1589_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4));
v___x_1590_ = lean_string_append(v___x_1588_, v___x_1589_);
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
return v___x_1591_;
}
v___jp_1592_:
{
switch(lean_obj_tag(v_a_1593_))
{
case 2:
{
lean_object* v_n_1594_; lean_object* v_mantissa_1595_; lean_object* v_exponent_1596_; lean_object* v_natZero_1597_; lean_object* v_intZero_1598_; uint8_t v_isNeg_1599_; 
v_n_1594_ = lean_ctor_get(v_a_1593_, 0);
v_mantissa_1595_ = lean_ctor_get(v_n_1594_, 0);
v_exponent_1596_ = lean_ctor_get(v_n_1594_, 1);
v_natZero_1597_ = lean_unsigned_to_nat(0u);
v_intZero_1598_ = lean_obj_once(&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6, &l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6_once, _init_l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6);
v_isNeg_1599_ = lean_int_dec_lt(v_mantissa_1595_, v_intZero_1598_);
if (v_isNeg_1599_ == 0)
{
uint8_t v___x_1600_; 
v___x_1600_ = lean_nat_dec_eq(v_exponent_1596_, v_natZero_1597_);
if (v___x_1600_ == 0)
{
v_ver_1584_ = v_a_1593_;
goto v___jp_1583_;
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1602_; 
lean_inc(v_mantissa_1595_);
lean_dec_ref(v_a_1593_);
v_a_1601_ = lean_nat_abs(v_mantissa_1595_);
lean_dec(v_mantissa_1595_);
v___x_1602_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1602_, 0, v_natZero_1597_);
lean_ctor_set(v___x_1602_, 1, v_a_1601_);
lean_ctor_set(v___x_1602_, 2, v_natZero_1597_);
v_ver_1566_ = v___x_1602_;
v_major_1567_ = v_natZero_1597_;
goto v___jp_1565_;
}
}
else
{
v_ver_1584_ = v_a_1593_;
goto v___jp_1583_;
}
}
case 3:
{
lean_object* v_s_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v_s_1603_ = lean_ctor_get(v_a_1593_, 0);
lean_inc_ref(v_s_1603_);
lean_dec_ref(v_a_1593_);
v___x_1604_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7));
v___x_1605_ = lean_unsigned_to_nat(0u);
v___x_1606_ = lean_string_utf8_byte_size(v_s_1603_);
v___x_1607_ = l___private_Lake_Util_Version_0__Lake_runVerParse(lean_box(0), v_s_1603_, v___x_1604_, v___x_1605_, v___x_1606_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1607_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1607_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v_toSemVerCore_1617_; lean_object* v_major_1618_; 
v_a_1616_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1616_);
lean_dec_ref(v___x_1607_);
v_toSemVerCore_1617_ = lean_ctor_get(v_a_1616_, 0);
lean_inc_ref(v_toSemVerCore_1617_);
lean_dec(v_a_1616_);
v_major_1618_ = lean_ctor_get(v_toSemVerCore_1617_, 0);
lean_inc(v_major_1618_);
v_ver_1566_ = v_toSemVerCore_1617_;
v_major_1567_ = v_major_1618_;
goto v___jp_1565_;
}
}
default: 
{
v_ver_1584_ = v_a_1593_;
goto v___jp_1583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___boxed(lean_object* v_obj_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_obj_1626_);
lean_dec(v_obj_1626_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(size_t v_sz_1628_, size_t v_i_1629_, lean_object* v_bs_1630_){
_start:
{
uint8_t v___x_1631_; 
v___x_1631_ = lean_usize_dec_lt(v_i_1629_, v_sz_1628_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; 
v___x_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1632_, 0, v_bs_1630_);
return v___x_1632_;
}
else
{
lean_object* v_v_1633_; lean_object* v___x_1634_; 
v_v_1633_ = lean_array_uget_borrowed(v_bs_1630_, v_i_1629_);
lean_inc(v_v_1633_);
v___x_1634_ = l_Lake_PackageEntry_fromJson_x3f(v_v_1633_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_dec_ref(v_bs_1630_);
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1644_; lean_object* v_bs_x27_1645_; size_t v___x_1646_; size_t v___x_1647_; lean_object* v___x_1648_; 
v_a_1643_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1643_);
lean_dec_ref(v___x_1634_);
v___x_1644_ = lean_unsigned_to_nat(0u);
v_bs_x27_1645_ = lean_array_uset(v_bs_1630_, v_i_1629_, v___x_1644_);
v___x_1646_ = ((size_t)1ULL);
v___x_1647_ = lean_usize_add(v_i_1629_, v___x_1646_);
v___x_1648_ = lean_array_uset(v_bs_x27_1645_, v_i_1629_, v_a_1643_);
v_i_1629_ = v___x_1647_;
v_bs_1630_ = v___x_1648_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_1650_, lean_object* v_i_1651_, lean_object* v_bs_1652_){
_start:
{
size_t v_sz_boxed_1653_; size_t v_i_boxed_1654_; lean_object* v_res_1655_; 
v_sz_boxed_1653_ = lean_unbox_usize(v_sz_1650_);
lean_dec(v_sz_1650_);
v_i_boxed_1654_ = lean_unbox_usize(v_i_1651_);
lean_dec(v_i_1651_);
v_res_1655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(v_sz_boxed_1653_, v_i_boxed_1654_, v_bs_1652_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1(lean_object* v_x_1657_){
_start:
{
if (lean_obj_tag(v_x_1657_) == 4)
{
lean_object* v_elems_1658_; size_t v_sz_1659_; size_t v___x_1660_; lean_object* v___x_1661_; 
v_elems_1658_ = lean_ctor_get(v_x_1657_, 0);
lean_inc_ref(v_elems_1658_);
lean_dec_ref(v_x_1657_);
v_sz_1659_ = lean_array_size(v_elems_1658_);
v___x_1660_ = ((size_t)0ULL);
v___x_1661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(v_sz_1659_, v___x_1660_, v_elems_1658_);
return v___x_1661_;
}
else
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1662_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1___closed__0));
v___x_1663_ = lean_unsigned_to_nat(80u);
v___x_1664_ = l_Lean_Json_pretty(v_x_1657_, v___x_1663_);
v___x_1665_ = lean_string_append(v___x_1662_, v___x_1664_);
lean_dec_ref(v___x_1664_);
v___x_1666_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1667_ = lean_string_append(v___x_1665_, v___x_1666_);
v___x_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
return v___x_1668_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1(lean_object* v_x_1671_){
_start:
{
if (lean_obj_tag(v_x_1671_) == 0)
{
lean_object* v___x_1672_; 
v___x_1672_ = ((lean_object*)(l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1___closed__0));
return v___x_1672_;
}
else
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1(v_x_1671_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1673_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1673_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
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
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1690_; 
v_a_1682_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1684_ = v___x_1673_;
v_isShared_1685_ = v_isSharedCheck_1690_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1673_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1690_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1686_, 0, v_a_1682_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v___x_1686_);
v___x_1688_ = v___x_1684_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(size_t v_sz_1691_, size_t v_i_1692_, lean_object* v_bs_1693_){
_start:
{
uint8_t v___x_1694_; 
v___x_1694_ = lean_usize_dec_lt(v_i_1692_, v_sz_1691_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1695_, 0, v_bs_1693_);
return v___x_1695_;
}
else
{
lean_object* v_v_1696_; lean_object* v___x_1697_; 
v_v_1696_ = lean_array_uget_borrowed(v_bs_1693_, v_i_1692_);
lean_inc(v_v_1696_);
v___x_1697_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson(v_v_1696_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec_ref(v_bs_1693_);
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1697_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1707_; lean_object* v_bs_x27_1708_; size_t v___x_1709_; size_t v___x_1710_; lean_object* v___x_1711_; 
v_a_1706_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_a_1706_);
lean_dec_ref(v___x_1697_);
v___x_1707_ = lean_unsigned_to_nat(0u);
v_bs_x27_1708_ = lean_array_uset(v_bs_1693_, v_i_1692_, v___x_1707_);
v___x_1709_ = ((size_t)1ULL);
v___x_1710_ = lean_usize_add(v_i_1692_, v___x_1709_);
v___x_1711_ = lean_array_uset(v_bs_x27_1708_, v_i_1692_, v_a_1706_);
v_i_1692_ = v___x_1710_;
v_bs_1693_ = v___x_1711_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_1713_, lean_object* v_i_1714_, lean_object* v_bs_1715_){
_start:
{
size_t v_sz_boxed_1716_; size_t v_i_boxed_1717_; lean_object* v_res_1718_; 
v_sz_boxed_1716_ = lean_unbox_usize(v_sz_1713_);
lean_dec(v_sz_1713_);
v_i_boxed_1717_ = lean_unbox_usize(v_i_1714_);
lean_dec(v_i_1714_);
v_res_1718_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(v_sz_boxed_1716_, v_i_boxed_1717_, v_bs_1715_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3(lean_object* v_x_1719_){
_start:
{
if (lean_obj_tag(v_x_1719_) == 4)
{
lean_object* v_elems_1720_; size_t v_sz_1721_; size_t v___x_1722_; lean_object* v___x_1723_; 
v_elems_1720_ = lean_ctor_get(v_x_1719_, 0);
lean_inc_ref(v_elems_1720_);
lean_dec_ref(v_x_1719_);
v_sz_1721_ = lean_array_size(v_elems_1720_);
v___x_1722_ = ((size_t)0ULL);
v___x_1723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(v_sz_1721_, v___x_1722_, v_elems_1720_);
return v___x_1723_;
}
else
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1724_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1___closed__0));
v___x_1725_ = lean_unsigned_to_nat(80u);
v___x_1726_ = l_Lean_Json_pretty(v_x_1719_, v___x_1725_);
v___x_1727_ = lean_string_append(v___x_1724_, v___x_1726_);
lean_dec_ref(v___x_1726_);
v___x_1728_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1729_ = lean_string_append(v___x_1727_, v___x_1728_);
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
return v___x_1730_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2(lean_object* v_x_1733_){
_start:
{
if (lean_obj_tag(v_x_1733_) == 0)
{
lean_object* v___x_1734_; 
v___x_1734_ = ((lean_object*)(l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2___closed__0));
return v___x_1734_;
}
else
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3(v_x_1733_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1735_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1735_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1752_; 
v_a_1744_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1746_ = v___x_1735_;
v_isShared_1747_ = v_isSharedCheck_1752_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1735_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1752_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1748_, 0, v_a_1744_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 0, v___x_1748_);
v___x_1750_ = v___x_1746_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(size_t v_sz_1753_, size_t v_i_1754_, lean_object* v_bs_1755_){
_start:
{
uint8_t v___x_1756_; 
v___x_1756_ = lean_usize_dec_lt(v_i_1754_, v_sz_1753_);
if (v___x_1756_ == 0)
{
return v_bs_1755_;
}
else
{
lean_object* v_v_1757_; lean_object* v___x_1758_; lean_object* v_bs_x27_1759_; lean_object* v___x_1760_; size_t v___x_1761_; size_t v___x_1762_; lean_object* v___x_1763_; 
v_v_1757_ = lean_array_uget(v_bs_1755_, v_i_1754_);
v___x_1758_ = lean_unsigned_to_nat(0u);
v_bs_x27_1759_ = lean_array_uset(v_bs_1755_, v_i_1754_, v___x_1758_);
v___x_1760_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(v_v_1757_);
lean_dec(v_v_1757_);
v___x_1761_ = ((size_t)1ULL);
v___x_1762_ = lean_usize_add(v_i_1754_, v___x_1761_);
v___x_1763_ = lean_array_uset(v_bs_x27_1759_, v_i_1754_, v___x_1760_);
v_i_1754_ = v___x_1762_;
v_bs_1755_ = v___x_1763_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0___boxed(lean_object* v_sz_1765_, lean_object* v_i_1766_, lean_object* v_bs_1767_){
_start:
{
size_t v_sz_boxed_1768_; size_t v_i_boxed_1769_; lean_object* v_res_1770_; 
v_sz_boxed_1768_ = lean_unbox_usize(v_sz_1765_);
lean_dec(v_sz_1765_);
v_i_boxed_1769_ = lean_unbox_usize(v_i_1766_);
lean_dec(v_i_1766_);
v_res_1770_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(v_sz_boxed_1768_, v_i_boxed_1769_, v_bs_1767_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(lean_object* v_ver_1784_, lean_object* v_obj_1785_){
_start:
{
lean_object* v_a_1787_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1796_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__4));
v___x_1797_ = l_Lake_StdVer_compare(v_ver_1784_, v___x_1796_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__7));
v___x_1799_ = l_Lake_JsonObject_getJson_x3f(v_obj_1785_, v___x_1798_);
if (lean_obj_tag(v___x_1799_) == 0)
{
goto v___jp_1792_;
}
else
{
lean_object* v_val_1800_; lean_object* v___x_1801_; 
v_val_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_val_1800_);
lean_dec_ref(v___x_1799_);
v___x_1801_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2(v_val_1800_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1811_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1811_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1811_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1809_; 
v___x_1806_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5));
v___x_1807_ = lean_string_append(v___x_1806_, v_a_1802_);
lean_dec(v_a_1802_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1807_);
v___x_1809_ = v___x_1804_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
else
{
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
v_a_1812_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1801_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1801_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set_tag(v___x_1814_, 0);
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
else
{
lean_object* v_a_1820_; 
v_a_1820_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1820_);
lean_dec_ref(v___x_1801_);
if (lean_obj_tag(v_a_1820_) == 0)
{
goto v___jp_1792_;
}
else
{
lean_object* v_val_1821_; 
v_val_1821_ = lean_ctor_get(v_a_1820_, 0);
lean_inc(v_val_1821_);
lean_dec_ref(v_a_1820_);
v_a_1787_ = v_val_1821_;
goto v___jp_1786_;
}
}
}
}
}
else
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__7));
v___x_1823_ = l_Lake_JsonObject_getJson_x3f(v_obj_1785_, v___x_1822_);
if (lean_obj_tag(v___x_1823_) == 0)
{
goto v___jp_1794_;
}
else
{
lean_object* v_val_1824_; lean_object* v___x_1825_; 
v_val_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_val_1824_);
lean_dec_ref(v___x_1823_);
v___x_1825_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1(v_val_1824_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1835_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1828_ = v___x_1825_;
v_isShared_1829_ = v_isSharedCheck_1835_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1825_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1835_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1830_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5));
v___x_1831_ = lean_string_append(v___x_1830_, v_a_1826_);
lean_dec(v_a_1826_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___x_1831_);
v___x_1833_ = v___x_1828_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
else
{
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
v_a_1836_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1825_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1825_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
lean_ctor_set_tag(v___x_1838_, 0);
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1852_; 
v_a_1844_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1846_ = v___x_1825_;
v_isShared_1847_ = v_isSharedCheck_1852_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1825_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1852_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
if (lean_obj_tag(v_a_1844_) == 0)
{
lean_del_object(v___x_1846_);
goto v___jp_1794_;
}
else
{
lean_object* v_val_1848_; lean_object* v___x_1850_; 
v_val_1848_ = lean_ctor_get(v_a_1844_, 0);
lean_inc(v_val_1848_);
lean_dec_ref(v_a_1844_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v_val_1848_);
v___x_1850_ = v___x_1846_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_val_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
}
}
}
v___jp_1786_:
{
size_t v_sz_1788_; size_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v_sz_1788_ = lean_array_size(v_a_1787_);
v___x_1789_ = ((size_t)0ULL);
v___x_1790_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(v_sz_1788_, v___x_1789_, v_a_1787_);
v___x_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
return v___x_1791_;
}
v___jp_1792_:
{
lean_object* v___x_1793_; 
v___x_1793_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__0));
v_a_1787_ = v___x_1793_;
goto v___jp_1786_;
}
v___jp_1794_:
{
lean_object* v___x_1795_; 
v___x_1795_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__2));
return v___x_1795_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___boxed(lean_object* v_ver_1853_, lean_object* v_obj_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(v_ver_1853_, v_obj_1854_);
lean_dec(v_obj_1854_);
lean_dec_ref(v_ver_1853_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0(lean_object* v_x_1858_){
_start:
{
if (lean_obj_tag(v_x_1858_) == 0)
{
lean_object* v___x_1859_; 
v___x_1859_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0___closed__0));
return v___x_1859_;
}
else
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Lean_Name_fromJson_x3f(v_x_1858_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1877_; 
v_a_1869_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1871_ = v___x_1860_;
v_isShared_1872_ = v_isSharedCheck_1877_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1860_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1877_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v___x_1875_; 
v___x_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1873_, 0, v_a_1869_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1873_);
v___x_1875_ = v___x_1871_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1873_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1(lean_object* v_x_1880_){
_start:
{
if (lean_obj_tag(v_x_1880_) == 0)
{
lean_object* v___x_1881_; 
v___x_1881_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1___closed__0));
return v___x_1881_;
}
else
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_Json_getBool_x3f(v_x_1880_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1882_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1899_; 
v_a_1891_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1893_ = v___x_1882_;
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1882_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1895_; lean_object* v___x_1897_; 
v___x_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1895_, 0, v_a_1891_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v___x_1895_);
v___x_1897_ = v___x_1893_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1895_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1___boxed(lean_object* v_x_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1(v_x_1900_);
lean_dec(v_x_1900_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_fromJson_x3f(lean_object* v_json_1905_){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Lean_Json_getObj_x3f(v_json_1905_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1916_; 
v_a_1915_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1915_);
lean_dec_ref(v___x_1906_);
v___x_1916_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_a_1915_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_a_1915_);
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1916_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
else
{
lean_object* v_a_1925_; uint8_t v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v_a_1930_; uint8_t v___y_1952_; lean_object* v___y_1953_; lean_object* v_a_1954_; uint8_t v___y_1980_; lean_object* v___y_1981_; uint8_t v___y_1984_; lean_object* v_a_1985_; uint8_t v___y_2011_; uint8_t v_a_2014_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v_a_1925_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1925_);
lean_dec_ref(v___x_1916_);
v___x_2041_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__4));
v___x_2042_ = l_Lake_JsonObject_getJson_x3f(v_a_1915_, v___x_2041_);
if (lean_obj_tag(v___x_2042_) == 0)
{
goto v___jp_2039_;
}
else
{
lean_object* v_val_2043_; lean_object* v___x_2044_; 
v_val_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_val_2043_);
lean_dec_ref(v___x_2042_);
v___x_2044_ = l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1(v_val_2043_);
lean_dec(v_val_2043_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2054_; 
lean_dec(v_a_1925_);
lean_dec(v_a_1915_);
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2047_ = v___x_2044_;
v_isShared_2048_ = v_isSharedCheck_2054_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2044_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2054_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2052_; 
v___x_2049_ = ((lean_object*)(l_Lake_Manifest_fromJson_x3f___closed__2));
v___x_2050_ = lean_string_append(v___x_2049_, v_a_2045_);
lean_dec(v_a_2045_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 0, v___x_2050_);
v___x_2052_ = v___x_2047_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
else
{
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec(v_a_1925_);
lean_dec(v_a_1915_);
v_a_2055_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2044_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2044_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
lean_ctor_set_tag(v___x_2057_, 0);
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
else
{
lean_object* v_a_2063_; 
v_a_2063_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2063_);
lean_dec_ref(v___x_2044_);
if (lean_obj_tag(v_a_2063_) == 0)
{
goto v___jp_2039_;
}
else
{
lean_object* v_val_2064_; uint8_t v___x_2065_; 
v_val_2064_ = lean_ctor_get(v_a_2063_, 0);
lean_inc(v_val_2064_);
lean_dec_ref(v_a_2063_);
v___x_2065_ = lean_unbox(v_val_2064_);
lean_dec(v_val_2064_);
v_a_2014_ = v___x_2065_;
goto v___jp_2013_;
}
}
}
}
v___jp_1926_:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1931_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v_a_1925_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(v___x_1932_, v_a_1915_);
lean_dec(v_a_1915_);
lean_dec_ref(v___x_1932_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_dec(v_a_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1950_; 
v_a_1942_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1944_ = v___x_1933_;
v_isShared_1945_ = v_isSharedCheck_1950_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1933_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1950_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; lean_object* v___x_1948_; 
v___x_1946_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1946_, 0, v___y_1929_);
lean_ctor_set(v___x_1946_, 1, v___y_1928_);
lean_ctor_set(v___x_1946_, 2, v_a_1930_);
lean_ctor_set(v___x_1946_, 3, v_a_1942_);
lean_ctor_set_uint8(v___x_1946_, sizeof(void*)*4, v___y_1927_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 0, v___x_1946_);
v___x_1948_ = v___x_1944_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1946_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
v___jp_1951_:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__6));
v___x_1956_ = l_Lake_JsonObject_getJson_x3f(v_a_1915_, v___x_1955_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v___x_1957_; 
v___x_1957_ = lean_box(0);
v___y_1927_ = v___y_1952_;
v___y_1928_ = v_a_1954_;
v___y_1929_ = v___y_1953_;
v_a_1930_ = v___x_1957_;
goto v___jp_1926_;
}
else
{
lean_object* v_val_1958_; lean_object* v___x_1959_; 
v_val_1958_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_val_1958_);
lean_dec_ref(v___x_1956_);
v___x_1959_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1958_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1969_; 
lean_dec_ref(v_a_1954_);
lean_dec(v___y_1953_);
lean_dec(v_a_1925_);
lean_dec(v_a_1915_);
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1962_ = v___x_1959_;
v_isShared_1963_ = v_isSharedCheck_1969_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1959_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1969_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1964_ = ((lean_object*)(l_Lake_Manifest_fromJson_x3f___closed__0));
v___x_1965_ = lean_string_append(v___x_1964_, v_a_1960_);
lean_dec(v_a_1960_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1965_);
v___x_1967_ = v___x_1962_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
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
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_dec_ref(v_a_1954_);
lean_dec(v___y_1953_);
lean_dec(v_a_1925_);
lean_dec(v_a_1915_);
v_a_1970_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1959_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1959_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
lean_ctor_set_tag(v___x_1972_, 0);
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
else
{
lean_object* v_a_1978_; 
v_a_1978_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1978_);
lean_dec_ref(v___x_1959_);
v___y_1927_ = v___y_1952_;
v___y_1928_ = v_a_1954_;
v___y_1929_ = v___y_1953_;
v_a_1930_ = v_a_1978_;
goto v___jp_1926_;
}
}
}
}
v___jp_1979_:
{
lean_object* v___x_1982_; 
v___x_1982_ = l_Lake_defaultLakeDir;
v___y_1952_ = v___y_1980_;
v___y_1953_ = v___y_1981_;
v_a_1954_ = v___x_1982_;
goto v___jp_1951_;
}
v___jp_1983_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__5));
v___x_1987_ = l_Lake_JsonObject_getJson_x3f(v_a_1915_, v___x_1986_);
if (lean_obj_tag(v___x_1987_) == 0)
{
v___y_1980_ = v___y_1984_;
v___y_1981_ = v_a_1985_;
goto v___jp_1979_;
}
else
{
lean_object* v_val_1988_; lean_object* v___x_1989_; 
v_val_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_val_1988_);
lean_dec_ref(v___x_1987_);
v___x_1989_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1988_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1999_; 
lean_dec(v_a_1985_);
lean_dec(v_a_1925_);
lean_dec(v_a_1915_);
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_1999_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1999_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1997_; 
v___x_1994_ = ((lean_object*)(l_Lake_Manifest_fromJson_x3f___closed__1));
v___x_1995_ = lean_string_append(v___x_1994_, v_a_1990_);
lean_dec(v_a_1990_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_1995_);
v___x_1997_ = v___x_1992_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
else
{
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v_a_1985_);
lean_dec(v_a_1925_);
lean_dec(v_a_1915_);
v_a_2000_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1989_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1989_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set_tag(v___x_2002_, 0);
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
else
{
lean_object* v_a_2008_; 
v_a_2008_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_2008_);
lean_dec_ref(v___x_1989_);
if (lean_obj_tag(v_a_2008_) == 0)
{
v___y_1980_ = v___y_1984_;
v___y_1981_ = v_a_1985_;
goto v___jp_1979_;
}
else
{
lean_object* v_val_2009_; 
v_val_2009_ = lean_ctor_get(v_a_2008_, 0);
lean_inc(v_val_2009_);
lean_dec_ref(v_a_2008_);
v___y_1952_ = v___y_1984_;
v___y_1953_ = v_a_1985_;
v_a_1954_ = v_val_2009_;
goto v___jp_1951_;
}
}
}
}
}
v___jp_2010_:
{
lean_object* v___x_2012_; 
v___x_2012_ = lean_box(0);
v___y_1984_ = v___y_2011_;
v_a_1985_ = v___x_2012_;
goto v___jp_1983_;
}
v___jp_2013_:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_2016_ = l_Lake_JsonObject_getJson_x3f(v_a_1915_, v___x_2015_);
if (lean_obj_tag(v___x_2016_) == 0)
{
v___y_2011_ = v_a_2014_;
goto v___jp_2010_;
}
else
{
lean_object* v_val_2017_; lean_object* v___x_2018_; 
v_val_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_val_2017_);
lean_dec_ref(v___x_2016_);
v___x_2018_ = l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0(v_val_2017_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2028_; 
lean_dec(v_a_1925_);
lean_dec(v_a_1915_);
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2021_ = v___x_2018_;
v_isShared_2022_ = v_isSharedCheck_2028_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2018_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2028_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2023_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__1));
v___x_2024_ = lean_string_append(v___x_2023_, v_a_2019_);
lean_dec(v_a_2019_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2024_);
v___x_2026_ = v___x_2021_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
else
{
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v_a_1925_);
lean_dec(v_a_1915_);
v_a_2029_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2018_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2018_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
lean_ctor_set_tag(v___x_2031_, 0);
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
else
{
lean_object* v_a_2037_; 
v_a_2037_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2037_);
lean_dec_ref(v___x_2018_);
if (lean_obj_tag(v_a_2037_) == 0)
{
v___y_2011_ = v_a_2014_;
goto v___jp_2010_;
}
else
{
lean_object* v_val_2038_; 
v_val_2038_ = lean_ctor_get(v_a_2037_, 0);
lean_inc(v_val_2038_);
lean_dec_ref(v_a_2037_);
v___y_1984_ = v_a_2014_;
v_a_1985_ = v_val_2038_;
goto v___jp_1983_;
}
}
}
}
}
v___jp_2039_:
{
uint8_t v___x_2040_; 
v___x_2040_ = 0;
v_a_2014_ = v___x_2040_;
goto v___jp_2013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_parse(lean_object* v_data_2069_){
_start:
{
lean_object* v___x_2070_; 
v___x_2070_ = l_Lean_Json_parse(v_data_2069_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2080_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2073_ = v___x_2070_;
v_isShared_2074_ = v_isSharedCheck_2080_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2070_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2080_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2075_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2076_ = lean_string_append(v___x_2075_, v_a_2071_);
lean_dec(v_a_2071_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2076_);
v___x_2078_ = v___x_2073_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2082_; 
v_a_2081_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2081_);
lean_dec_ref(v___x_2070_);
v___x_2082_ = l_Lake_Manifest_fromJson_x3f(v_a_2081_);
return v___x_2082_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load(lean_object* v_file_2084_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l_IO_FS_readFile(v_file_2084_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2115_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2089_ = v___x_2086_;
v_isShared_2090_ = v_isSharedCheck_2115_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2086_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2115_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v_a_2092_; lean_object* v___x_2100_; 
v___x_2100_ = l_Lean_Json_parse(v_a_2087_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref(v___x_2100_);
v___x_2102_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2103_ = lean_string_append(v___x_2102_, v_a_2101_);
lean_dec(v_a_2101_);
v_a_2092_ = v___x_2103_;
goto v___jp_2091_;
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2105_; 
v_a_2104_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2104_);
lean_dec_ref(v___x_2100_);
v___x_2105_ = l_Lake_Manifest_fromJson_x3f(v_a_2104_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref(v___x_2105_);
v_a_2092_ = v_a_2106_;
goto v___jp_2091_;
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_del_object(v___x_2089_);
lean_dec_ref(v_file_2084_);
v_a_2107_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2105_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2105_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set_tag(v___x_2109_, 0);
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
v___jp_2091_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2098_; 
v___x_2093_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2094_ = lean_string_append(v_file_2084_, v___x_2093_);
v___x_2095_ = lean_string_append(v___x_2094_, v_a_2092_);
lean_dec_ref(v_a_2092_);
v___x_2096_ = lean_mk_io_user_error(v___x_2095_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set_tag(v___x_2089_, 1);
lean_ctor_set(v___x_2089_, 0, v___x_2096_);
v___x_2098_ = v___x_2089_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec_ref(v_file_2084_);
v_a_2116_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2086_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2086_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load___boxed(lean_object* v_file_2124_, lean_object* v_a_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l_Lake_Manifest_load(v_file_2124_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f(lean_object* v_file_2127_){
_start:
{
lean_object* v_a_2130_; lean_object* v___x_2134_; 
v___x_2134_ = l_IO_FS_readFile(v_file_2127_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2163_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2137_ = v___x_2134_;
v_isShared_2138_ = v_isSharedCheck_2163_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2134_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2163_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v_a_2140_; lean_object* v___x_2145_; 
v___x_2145_ = l_Lean_Json_parse(v_a_2135_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
lean_del_object(v___x_2137_);
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2146_);
lean_dec_ref(v___x_2145_);
v___x_2147_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2148_ = lean_string_append(v___x_2147_, v_a_2146_);
lean_dec(v_a_2146_);
v_a_2140_ = v___x_2148_;
goto v___jp_2139_;
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2150_; 
v_a_2149_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2149_);
lean_dec_ref(v___x_2145_);
v___x_2150_ = l_Lake_Manifest_fromJson_x3f(v_a_2149_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; 
lean_del_object(v___x_2137_);
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref(v___x_2150_);
v_a_2140_ = v_a_2151_;
goto v___jp_2139_;
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2162_; 
lean_dec_ref(v_file_2127_);
v_a_2152_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2154_ = v___x_2150_;
v_isShared_2155_ = v_isSharedCheck_2162_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2150_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2162_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
lean_object* v___x_2159_; 
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2157_);
v___x_2159_ = v___x_2137_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
}
v___jp_2139_:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2141_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2142_ = lean_string_append(v_file_2127_, v___x_2141_);
v___x_2143_ = lean_string_append(v___x_2142_, v_a_2140_);
lean_dec_ref(v_a_2140_);
v___x_2144_ = lean_mk_io_user_error(v___x_2143_);
v_a_2130_ = v___x_2144_;
goto v___jp_2129_;
}
}
}
else
{
lean_object* v_a_2164_; 
lean_dec_ref(v_file_2127_);
v_a_2164_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2164_);
lean_dec_ref(v___x_2134_);
v_a_2130_ = v_a_2164_;
goto v___jp_2129_;
}
v___jp_2129_:
{
if (lean_obj_tag(v_a_2130_) == 11)
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
lean_dec_ref(v_a_2130_);
v___x_2131_ = lean_box(0);
v___x_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
return v___x_2132_;
}
else
{
lean_object* v___x_2133_; 
v___x_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2133_, 0, v_a_2130_);
return v___x_2133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f___boxed(lean_object* v_file_2165_, lean_object* v_a_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Lake_Manifest_load_x3f(v_file_2165_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_save(lean_object* v_self_2168_, lean_object* v_manifestFile_2169_){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v_contents_2173_; uint32_t v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2171_ = l_Lake_Manifest_toJson(v_self_2168_);
v___x_2172_ = lean_unsigned_to_nat(80u);
v_contents_2173_ = l_Lean_Json_pretty(v___x_2171_, v___x_2172_);
v___x_2174_ = 10;
v___x_2175_ = lean_string_push(v_contents_2173_, v___x_2174_);
v___x_2176_ = l_IO_FS_writeFile(v_manifestFile_2169_, v___x_2175_);
lean_dec_ref(v___x_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_save___boxed(lean_object* v_self_2177_, lean_object* v_manifestFile_2178_, lean_object* v_a_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Lake_Manifest_save(v_self_2177_, v_manifestFile_2178_);
lean_dec_ref(v_manifestFile_2178_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_decodeEntries(lean_object* v_data_2181_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_Json_getObj_x3f(v_data_2181_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2182_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2182_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2192_; 
v_a_2191_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2191_);
lean_dec_ref(v___x_2182_);
v___x_2192_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_a_2191_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec(v_a_2191_);
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2192_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2192_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v_a_2201_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2201_);
lean_dec_ref(v___x_2192_);
v___x_2202_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_2203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2203_, 0, v_a_2201_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
v___x_2204_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(v___x_2203_, v_a_2191_);
lean_dec(v_a_2191_);
lean_dec_ref(v___x_2203_);
return v___x_2204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_parseEntries(lean_object* v_data_2205_){
_start:
{
lean_object* v___x_2206_; 
v___x_2206_ = l_Lean_Json_parse(v_data_2205_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2216_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2209_ = v___x_2206_;
v_isShared_2210_ = v_isSharedCheck_2216_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2216_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2211_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2212_ = lean_string_append(v___x_2211_, v_a_2207_);
lean_dec(v_a_2207_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2212_);
v___x_2214_ = v___x_2209_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2218_; 
v_a_2217_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_a_2217_);
lean_dec_ref(v___x_2206_);
v___x_2218_ = l_Lake_Manifest_decodeEntries(v_a_2217_);
return v___x_2218_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_loadEntries(lean_object* v_file_2219_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_IO_FS_readFile(v_file_2219_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2250_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2224_ = v___x_2221_;
v_isShared_2225_ = v_isSharedCheck_2250_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2221_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2250_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v_a_2227_; lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_Json_parse(v_a_2222_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref(v___x_2235_);
v___x_2237_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2238_ = lean_string_append(v___x_2237_, v_a_2236_);
lean_dec(v_a_2236_);
v_a_2227_ = v___x_2238_;
goto v___jp_2226_;
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2240_; 
v_a_2239_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2239_);
lean_dec_ref(v___x_2235_);
v___x_2240_ = l_Lake_Manifest_decodeEntries(v_a_2239_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2241_);
lean_dec_ref(v___x_2240_);
v_a_2227_ = v_a_2241_;
goto v___jp_2226_;
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
lean_del_object(v___x_2224_);
lean_dec_ref(v_file_2219_);
v_a_2242_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2240_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2240_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
lean_ctor_set_tag(v___x_2244_, 0);
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
v___jp_2226_:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2228_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2229_ = lean_string_append(v_file_2219_, v___x_2228_);
v___x_2230_ = lean_string_append(v___x_2229_, v_a_2227_);
lean_dec_ref(v_a_2227_);
v___x_2231_ = lean_mk_io_user_error(v___x_2230_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set_tag(v___x_2224_, 1);
lean_ctor_set(v___x_2224_, 0, v___x_2231_);
v___x_2233_ = v___x_2224_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_dec_ref(v_file_2219_);
v_a_2251_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2221_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2221_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_loadEntries___boxed(lean_object* v_file_2259_, lean_object* v_a_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lake_Manifest_loadEntries(v_file_2259_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries(lean_object* v_file_2262_){
_start:
{
lean_object* v_a_2265_; lean_object* v___x_2274_; 
v___x_2274_ = l_IO_FS_readFile(v_file_2262_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2296_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2277_ = v___x_2274_;
v_isShared_2278_ = v_isSharedCheck_2296_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2274_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2296_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v_a_2280_; lean_object* v___x_2285_; 
v___x_2285_ = l_Lean_Json_parse(v_a_2275_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
lean_del_object(v___x_2277_);
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref(v___x_2285_);
v___x_2287_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2288_ = lean_string_append(v___x_2287_, v_a_2286_);
lean_dec(v_a_2286_);
v_a_2280_ = v___x_2288_;
goto v___jp_2279_;
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2290_; 
v_a_2289_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2289_);
lean_dec_ref(v___x_2285_);
v___x_2290_ = l_Lake_Manifest_decodeEntries(v_a_2289_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; 
lean_del_object(v___x_2277_);
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2291_);
lean_dec_ref(v___x_2290_);
v_a_2280_ = v_a_2291_;
goto v___jp_2279_;
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; 
lean_dec_ref(v_file_2262_);
v_a_2292_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2292_);
lean_dec_ref(v___x_2290_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v_a_2292_);
v___x_2294_ = v___x_2277_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2292_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
v___jp_2279_:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2281_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
lean_inc_ref(v_file_2262_);
v___x_2282_ = lean_string_append(v_file_2262_, v___x_2281_);
v___x_2283_ = lean_string_append(v___x_2282_, v_a_2280_);
lean_dec_ref(v_a_2280_);
v___x_2284_ = lean_mk_io_user_error(v___x_2283_);
v_a_2265_ = v___x_2284_;
goto v___jp_2264_;
}
}
}
else
{
lean_object* v_a_2297_; 
v_a_2297_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_a_2297_);
lean_dec_ref(v___x_2274_);
v_a_2265_ = v_a_2297_;
goto v___jp_2264_;
}
v___jp_2264_:
{
if (lean_obj_tag(v_a_2265_) == 11)
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
lean_dec_ref(v_a_2265_);
lean_dec_ref(v_file_2262_);
v___x_2266_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__1));
v___x_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
return v___x_2267_;
}
else
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2268_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2269_ = lean_string_append(v_file_2262_, v___x_2268_);
v___x_2270_ = lean_io_error_to_string(v_a_2265_);
v___x_2271_ = lean_string_append(v___x_2269_, v___x_2270_);
lean_dec_ref(v___x_2270_);
v___x_2272_ = lean_mk_io_user_error(v___x_2271_);
v___x_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
return v___x_2273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries___boxed(lean_object* v_file_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lake_Manifest_tryLoadEntries(v_file_2298_);
return v_res_2300_;
}
}
static lean_object* _init_l_Lake_Manifest_saveEntries___closed__0(void){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2301_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__2, &l_Lake_Manifest_toJson___closed__2_once, _init_l_Lake_Manifest_toJson___closed__2);
v___x_2302_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8));
v___x_2303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
lean_ctor_set(v___x_2303_, 1, v___x_2301_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries(lean_object* v_file_2304_, lean_object* v_entries_2305_){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v_contents_2316_; uint32_t v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2307_ = lean_obj_once(&l_Lake_Manifest_saveEntries___closed__0, &l_Lake_Manifest_saveEntries___closed__0_once, _init_l_Lake_Manifest_saveEntries___closed__0);
v___x_2308_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__7));
v___x_2309_ = l_Array_toJson___at___00Lake_Manifest_toJson_spec__0(v_entries_2305_);
v___x_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2308_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
v___x_2311_ = lean_box(0);
v___x_2312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2310_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
v___x_2313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2307_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
v___x_2314_ = l_Lean_Json_mkObj(v___x_2313_);
v___x_2315_ = lean_unsigned_to_nat(80u);
v_contents_2316_ = l_Lean_Json_pretty(v___x_2314_, v___x_2315_);
v___x_2317_ = 10;
v___x_2318_ = lean_string_push(v_contents_2316_, v___x_2317_);
v___x_2319_ = l_IO_FS_writeFile(v_file_2304_, v___x_2318_);
lean_dec_ref(v___x_2318_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries___boxed(lean_object* v_file_2320_, lean_object* v_entries_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l_Lake_Manifest_saveEntries(v_file_2320_, v_entries_2321_);
lean_dec_ref(v_file_2320_);
return v_res_2323_;
}
}
lean_object* runtime_initialize_Lake_Util_Version(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Defaults(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Error(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_FilePath(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Coe(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Load_Manifest(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Util_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Defaults(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_JsonObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedPackageEntry_default = _init_l_Lake_instInhabitedPackageEntry_default();
lean_mark_persistent(l_Lake_instInhabitedPackageEntry_default);
l_Lake_instInhabitedPackageEntry = _init_l_Lake_instInhabitedPackageEntry();
lean_mark_persistent(l_Lake_instInhabitedPackageEntry);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Load_Manifest(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Util_Version(uint8_t builtin);
lean_object* initialize_Lake_Config_Defaults(uint8_t builtin);
lean_object* initialize_Lake_Util_Error(uint8_t builtin);
lean_object* initialize_Lake_Util_FilePath(uint8_t builtin);
lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Coe(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Manifest(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Defaults(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_JsonObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Manifest(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Load_Manifest(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Load_Manifest(builtin);
}
#ifdef __cplusplus
}
#endif
