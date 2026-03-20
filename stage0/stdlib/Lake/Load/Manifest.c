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
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
extern lean_object* l_System_instInhabitedFilePath_default;
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
static lean_once_cell_t l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6_default___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6_default;
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6;
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_path_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_path_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_git_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_git_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_instInhabitedPackageEntrySrc_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPackageEntrySrc_default___closed__0;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageEntrySrc_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageEntrySrc;
static lean_once_cell_t l_Lake_instInhabitedPackageEntry_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPackageEntry_default___closed__0;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageEntry_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageEntry;
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
v___x_437_ = lean_panic_fn(v___x_436_, v_msg_435_);
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
v___x_518_ = lean_nat_add(v___y_516_, v___y_517_);
lean_dec(v___y_517_);
lean_dec(v___y_516_);
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
lean_ctor_set(v___x_497_, 3, v___y_515_);
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
lean_ctor_set(v_reuseFailAlloc_523_, 3, v___y_515_);
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
v___y_515_ = v___x_529_;
v___y_516_ = v___x_530_;
v___y_517_ = v_size_531_;
goto v___jp_514_;
}
else
{
lean_object* v___x_532_; 
v___x_532_ = lean_unsigned_to_nat(0u);
v___y_515_ = v___x_529_;
v___y_516_ = v___x_530_;
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
v___x_694_ = lean_nat_add(v___y_692_, v___y_693_);
lean_dec(v___y_693_);
lean_dec(v___y_692_);
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
lean_ctor_set(v___x_673_, 3, v___y_691_);
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
lean_ctor_set(v_reuseFailAlloc_699_, 3, v___y_691_);
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
v___y_691_ = v___x_706_;
v___y_692_ = v___x_707_;
v___y_693_ = v_size_708_;
goto v___jp_690_;
}
else
{
lean_object* v___x_709_; 
v___x_709_ = lean_unsigned_to_nat(0u);
v___y_691_ = v___x_706_;
v___y_692_ = v___x_707_;
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
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6_default___closed__0(void){
_start:
{
lean_object* v___x_936_; uint8_t v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_936_ = l_System_instInhabitedFilePath_default;
v___x_937_ = 0;
v___x_938_ = lean_box(1);
v___x_939_ = lean_box(0);
v___x_940_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_940_, 0, v___x_939_);
lean_ctor_set(v___x_940_, 1, v___x_938_);
lean_ctor_set(v___x_940_, 2, v___x_936_);
lean_ctor_set_uint8(v___x_940_, sizeof(void*)*3, v___x_937_);
return v___x_940_;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6_default(void){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = lean_obj_once(&l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6_default___closed__0, &l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6_default___closed__0_once, _init_l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6_default___closed__0);
return v___x_941_;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6(void){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6_default;
return v___x_942_;
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
static lean_object* _init_l_Lake_instInhabitedPackageEntrySrc_default___closed__0(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = l_System_instInhabitedFilePath_default;
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntrySrc_default(void){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = lean_obj_once(&l_Lake_instInhabitedPackageEntrySrc_default___closed__0, &l_Lake_instInhabitedPackageEntrySrc_default___closed__0_once, _init_l_Lake_instInhabitedPackageEntrySrc_default___closed__0);
return v___x_987_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntrySrc(void){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lake_instInhabitedPackageEntrySrc_default;
return v___x_988_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntry_default___closed__0(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_989_ = l_Lake_instInhabitedPackageEntrySrc_default;
v___x_990_ = lean_box(0);
v___x_991_ = l_System_instInhabitedFilePath_default;
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
LEAN_EXPORT lean_object* l_Lake_PackageEntry_toJson(lean_object* v_entry_1014_){
_start:
{
lean_object* v_name_1015_; lean_object* v_scope_1016_; uint8_t v_inherited_1017_; lean_object* v_configFile_1018_; lean_object* v_manifestFile_x3f_1019_; lean_object* v_src_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v_fields_1044_; 
v_name_1015_ = lean_ctor_get(v_entry_1014_, 0);
lean_inc(v_name_1015_);
v_scope_1016_ = lean_ctor_get(v_entry_1014_, 1);
lean_inc_ref(v_scope_1016_);
v_inherited_1017_ = lean_ctor_get_uint8(v_entry_1014_, sizeof(void*)*5);
v_configFile_1018_ = lean_ctor_get(v_entry_1014_, 2);
lean_inc_ref(v_configFile_1018_);
v_manifestFile_x3f_1019_ = lean_ctor_get(v_entry_1014_, 3);
lean_inc(v_manifestFile_x3f_1019_);
v_src_1020_ = lean_ctor_get(v_entry_1014_, 4);
lean_inc_ref(v_src_1020_);
lean_dec_ref(v_entry_1014_);
v___x_1021_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_1022_ = 1;
v___x_1023_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1015_, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1021_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__0));
v___x_1027_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1027_, 0, v_scope_1016_);
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1026_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__1));
v___x_1030_ = l_Lake_mkRelPathString(v_configFile_1018_);
v___x_1031_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1029_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__2));
v___x_1034_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_manifestFile_x3f_1019_);
v___x_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10));
v___x_1037_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1037_, 0, v_inherited_1017_);
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = lean_box(0);
v___x_1040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1035_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1032_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1028_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v_fields_1044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_fields_1044_, 0, v___x_1025_);
lean_ctor_set(v_fields_1044_, 1, v___x_1043_);
if (lean_obj_tag(v_src_1020_) == 0)
{
lean_object* v_dir_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1060_; 
v_dir_1045_ = lean_ctor_get(v_src_1020_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_src_1020_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1047_ = v_src_1020_;
v_isShared_1048_ = v_isSharedCheck_1060_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_dir_1045_);
lean_dec(v_src_1020_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1060_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1053_; 
v___x_1049_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__5));
v___x_1050_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22));
v___x_1051_ = l_Lake_mkRelPathString(v_dir_1045_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set_tag(v___x_1047_, 3);
lean_ctor_set(v___x_1047_, 0, v___x_1051_);
v___x_1053_ = v___x_1047_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1050_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
lean_ctor_set(v___x_1055_, 1, v___x_1039_);
v___x_1056_ = l_List_appendTR___redArg(v_fields_1044_, v___x_1055_);
v___x_1057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1049_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = l_Lean_Json_mkObj(v___x_1057_);
return v___x_1058_;
}
}
}
else
{
lean_object* v_url_1061_; lean_object* v_rev_1062_; lean_object* v_inputRev_x3f_1063_; lean_object* v_subDir_x3f_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v_url_1061_ = lean_ctor_get(v_src_1020_, 0);
lean_inc_ref(v_url_1061_);
v_rev_1062_ = lean_ctor_get(v_src_1020_, 1);
lean_inc_ref(v_rev_1062_);
v_inputRev_x3f_1063_ = lean_ctor_get(v_src_1020_, 2);
lean_inc(v_inputRev_x3f_1063_);
v_subDir_x3f_1064_ = lean_ctor_get(v_src_1020_, 3);
lean_inc(v_subDir_x3f_1064_);
lean_dec_ref(v_src_1020_);
v___x_1065_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__7));
v___x_1066_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12));
v___x_1067_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1067_, 0, v_url_1061_);
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14));
v___x_1070_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1070_, 0, v_rev_1062_);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__8));
v___x_1073_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__1(v_inputRev_x3f_1063_);
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__9));
v___x_1076_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_subDir_x3f_1064_);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v___x_1039_);
v___x_1079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1074_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1071_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1068_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = l_List_appendTR___redArg(v_fields_1044_, v___x_1081_);
v___x_1083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1065_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = l_Lean_Json_mkObj(v___x_1083_);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0(lean_object* v_x_1088_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0));
v___x_1090_ = lean_string_append(v___x_1089_, v_x_1088_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0___boxed(lean_object* v_x_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_x_1091_);
lean_dec_ref(v_x_1091_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f(lean_object* v_json_1113_){
_start:
{
lean_object* v_a_1115_; lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_Json_getObj_x3f(v_json_1113_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1127_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1127_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1127_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1125_; 
v___x_1123_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_a_1119_);
lean_dec(v_a_1119_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v___x_1123_);
v___x_1125_ = v___x_1121_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
else
{
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
v_a_1128_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1118_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1118_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set_tag(v___x_1130_, 0);
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1358_; 
v_a_1136_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1138_ = v___x_1118_;
v_isShared_1139_ = v_isSharedCheck_1358_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1118_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1358_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_1141_ = l_Lake_JsonObject_getJson_x3f(v_a_1136_, v___x_1140_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v___x_1142_; 
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v___x_1142_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__0));
v_a_1115_ = v___x_1142_;
goto v___jp_1114_;
}
else
{
lean_object* v_val_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1357_; 
v_val_1143_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1145_ = v___x_1141_;
v_isShared_1146_ = v_isSharedCheck_1357_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_val_1143_);
lean_dec(v___x_1141_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1357_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_Name_fromJson_x3f(v_val_1143_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref(v___x_1147_);
v___x_1149_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__1));
v___x_1150_ = lean_string_append(v___x_1149_, v_a_1148_);
lean_dec(v_a_1148_);
v_a_1115_ = v___x_1150_;
goto v___jp_1114_;
}
else
{
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1151_; 
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v_a_1151_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1151_);
lean_dec_ref(v___x_1147_);
v_a_1115_ = v_a_1151_;
goto v___jp_1114_;
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1356_; 
v_a_1152_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1154_ = v___x_1147_;
v_isShared_1155_ = v_isSharedCheck_1356_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1147_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1356_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v_a_1157_; lean_object* v___y_1169_; uint8_t v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v_a_1173_; lean_object* v___y_1182_; lean_object* v___y_1183_; uint8_t v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v_a_1189_; lean_object* v___y_1192_; uint8_t v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v_a_1198_; lean_object* v___y_1210_; lean_object* v___y_1211_; uint8_t v___y_1212_; lean_object* v___y_1213_; lean_object* v_a_1214_; lean_object* v___y_1270_; uint8_t v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; uint8_t v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v_a_1279_; lean_object* v___y_1291_; uint8_t v___y_1292_; lean_object* v___y_1293_; lean_object* v_a_1296_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__0));
v___x_1333_ = l_Lake_JsonObject_getJson_x3f(v_a_1136_, v___x_1332_);
if (lean_obj_tag(v___x_1333_) == 0)
{
goto v___jp_1330_;
}
else
{
lean_object* v_val_1334_; lean_object* v___x_1335_; 
v_val_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_val_1334_);
lean_dec_ref(v___x_1333_);
v___x_1335_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(v_val_1334_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1345_; 
lean_del_object(v___x_1154_);
lean_dec(v_a_1152_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1338_ = v___x_1335_;
v_isShared_1339_ = v_isSharedCheck_1345_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1345_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1343_; 
v___x_1340_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__19));
v___x_1341_ = lean_string_append(v___x_1340_, v_a_1336_);
lean_dec(v_a_1336_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1341_);
v___x_1343_ = v___x_1338_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
else
{
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_del_object(v___x_1154_);
lean_dec(v_a_1152_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v_a_1346_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1335_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1335_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
lean_ctor_set_tag(v___x_1348_, 0);
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
else
{
lean_object* v_a_1354_; 
v_a_1354_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1354_);
lean_dec_ref(v___x_1335_);
if (lean_obj_tag(v_a_1354_) == 0)
{
goto v___jp_1330_;
}
else
{
lean_object* v_val_1355_; 
v_val_1355_ = lean_ctor_get(v_a_1354_, 0);
lean_inc(v_val_1355_);
lean_dec_ref(v_a_1354_);
v_a_1296_ = v_val_1355_;
goto v___jp_1295_;
}
}
}
}
v___jp_1156_:
{
lean_object* v___x_1158_; uint8_t v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1158_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__2));
v___x_1159_ = 1;
v___x_1160_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_1152_, v___x_1159_);
v___x_1161_ = lean_string_append(v___x_1158_, v___x_1160_);
lean_dec_ref(v___x_1160_);
v___x_1162_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__3));
v___x_1163_ = lean_string_append(v___x_1161_, v___x_1162_);
v___x_1164_ = lean_string_append(v___x_1163_, v_a_1157_);
lean_dec_ref(v_a_1157_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set_tag(v___x_1154_, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1164_);
v___x_1166_ = v___x_1154_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
v___jp_1168_:
{
lean_object* v___x_1175_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___y_1172_);
v___x_1175_ = v___x_1145_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___y_1172_);
v___x_1175_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1176_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1176_, 0, v_a_1152_);
lean_ctor_set(v___x_1176_, 1, v___y_1171_);
lean_ctor_set(v___x_1176_, 2, v___y_1169_);
lean_ctor_set(v___x_1176_, 3, v___x_1175_);
lean_ctor_set(v___x_1176_, 4, v_a_1173_);
lean_ctor_set_uint8(v___x_1176_, sizeof(void*)*5, v___y_1170_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1176_);
v___x_1178_ = v___x_1138_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
v___jp_1181_:
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1190_, 0, v___y_1186_);
lean_ctor_set(v___x_1190_, 1, v___y_1185_);
lean_ctor_set(v___x_1190_, 2, v___y_1188_);
lean_ctor_set(v___x_1190_, 3, v_a_1189_);
v___y_1169_ = v___y_1182_;
v___y_1170_ = v___y_1184_;
v___y_1171_ = v___y_1183_;
v___y_1172_ = v___y_1187_;
v_a_1173_ = v___x_1190_;
goto v___jp_1168_;
}
v___jp_1191_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__9));
v___x_1200_ = l_Lake_JsonObject_getJson_x3f(v_a_1136_, v___x_1199_);
lean_dec(v_a_1136_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v___x_1201_; 
lean_del_object(v___x_1154_);
v___x_1201_ = lean_box(0);
v___y_1182_ = v___y_1192_;
v___y_1183_ = v___y_1194_;
v___y_1184_ = v___y_1193_;
v___y_1185_ = v___y_1195_;
v___y_1186_ = v___y_1196_;
v___y_1187_ = v___y_1197_;
v___y_1188_ = v_a_1198_;
v_a_1189_ = v___x_1201_;
goto v___jp_1181_;
}
else
{
lean_object* v_val_1202_; lean_object* v___x_1203_; 
v_val_1202_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_val_1202_);
lean_dec_ref(v___x_1200_);
v___x_1203_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1202_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_dec(v_a_1198_);
lean_dec_ref(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec_ref(v___y_1192_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1204_);
lean_dec_ref(v___x_1203_);
v___x_1205_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__4));
v___x_1206_ = lean_string_append(v___x_1205_, v_a_1204_);
lean_dec(v_a_1204_);
v_a_1157_ = v___x_1206_;
goto v___jp_1156_;
}
else
{
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1207_; 
lean_dec(v_a_1198_);
lean_dec_ref(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec_ref(v___y_1192_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
v_a_1207_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1207_);
lean_dec_ref(v___x_1203_);
v_a_1157_ = v_a_1207_;
goto v___jp_1156_;
}
else
{
lean_object* v_a_1208_; 
lean_del_object(v___x_1154_);
v_a_1208_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1208_);
lean_dec_ref(v___x_1203_);
v___y_1182_ = v___y_1192_;
v___y_1183_ = v___y_1194_;
v___y_1184_ = v___y_1193_;
v___y_1185_ = v___y_1195_;
v___y_1186_ = v___y_1196_;
v___y_1187_ = v___y_1197_;
v___y_1188_ = v_a_1198_;
v_a_1189_ = v_a_1208_;
goto v___jp_1181_;
}
}
}
}
v___jp_1209_:
{
lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2));
v___x_1216_ = lean_string_dec_eq(v___y_1213_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; uint8_t v___x_1218_; 
v___x_1217_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3));
v___x_1218_ = lean_string_dec_eq(v___y_1213_, v___x_1217_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_dec_ref(v_a_1214_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v___x_1219_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__5));
v___x_1220_ = lean_string_append(v___x_1219_, v___y_1213_);
lean_dec_ref(v___y_1213_);
v___x_1221_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1222_ = lean_string_append(v___x_1220_, v___x_1221_);
v_a_1157_ = v___x_1222_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec_ref(v___y_1213_);
v___x_1223_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12));
v___x_1224_ = l_Lake_JsonObject_getJson_x3f(v_a_1136_, v___x_1223_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v___x_1225_; 
lean_dec_ref(v_a_1214_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v___x_1225_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__6));
v_a_1157_ = v___x_1225_;
goto v___jp_1156_;
}
else
{
lean_object* v_val_1226_; lean_object* v___x_1227_; 
v_val_1226_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_val_1226_);
lean_dec_ref(v___x_1224_);
v___x_1227_ = l_Lean_Json_getStr_x3f(v_val_1226_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
lean_dec_ref(v_a_1214_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1228_);
lean_dec_ref(v___x_1227_);
v___x_1229_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__7));
v___x_1230_ = lean_string_append(v___x_1229_, v_a_1228_);
lean_dec(v_a_1228_);
v_a_1157_ = v___x_1230_;
goto v___jp_1156_;
}
else
{
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1231_; 
lean_dec_ref(v_a_1214_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v_a_1231_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1231_);
lean_dec_ref(v___x_1227_);
v_a_1157_ = v_a_1231_;
goto v___jp_1156_;
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v_a_1232_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1232_);
lean_dec_ref(v___x_1227_);
v___x_1233_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14));
v___x_1234_ = l_Lake_JsonObject_getJson_x3f(v_a_1136_, v___x_1233_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v___x_1235_; 
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1214_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v___x_1235_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__8));
v_a_1157_ = v___x_1235_;
goto v___jp_1156_;
}
else
{
lean_object* v_val_1236_; lean_object* v___x_1237_; 
v_val_1236_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_val_1236_);
lean_dec_ref(v___x_1234_);
v___x_1237_ = l_Lean_Json_getStr_x3f(v_val_1236_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1214_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_a_1238_);
lean_dec_ref(v___x_1237_);
v___x_1239_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__9));
v___x_1240_ = lean_string_append(v___x_1239_, v_a_1238_);
lean_dec(v_a_1238_);
v_a_1157_ = v___x_1240_;
goto v___jp_1156_;
}
else
{
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1241_; 
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1214_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v_a_1241_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_a_1241_);
lean_dec_ref(v___x_1237_);
v_a_1157_ = v_a_1241_;
goto v___jp_1156_;
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v_a_1242_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_a_1242_);
lean_dec_ref(v___x_1237_);
v___x_1243_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__8));
v___x_1244_ = l_Lake_JsonObject_getJson_x3f(v_a_1136_, v___x_1243_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v___x_1245_; 
v___x_1245_ = lean_box(0);
v___y_1192_ = v___y_1210_;
v___y_1193_ = v___y_1212_;
v___y_1194_ = v___y_1211_;
v___y_1195_ = v_a_1242_;
v___y_1196_ = v_a_1232_;
v___y_1197_ = v_a_1214_;
v_a_1198_ = v___x_1245_;
goto v___jp_1191_;
}
else
{
lean_object* v_val_1246_; lean_object* v___x_1247_; 
v_val_1246_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_val_1246_);
lean_dec_ref(v___x_1244_);
v___x_1247_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(v_val_1246_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_dec(v_a_1242_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1214_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref(v___x_1247_);
v___x_1249_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__10));
v___x_1250_ = lean_string_append(v___x_1249_, v_a_1248_);
lean_dec(v_a_1248_);
v_a_1157_ = v___x_1250_;
goto v___jp_1156_;
}
else
{
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1251_; 
lean_dec(v_a_1242_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1214_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v_a_1251_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1251_);
lean_dec_ref(v___x_1247_);
v_a_1157_ = v_a_1251_;
goto v___jp_1156_;
}
else
{
lean_object* v_a_1252_; 
v_a_1252_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1252_);
lean_dec_ref(v___x_1247_);
v___y_1192_ = v___y_1210_;
v___y_1193_ = v___y_1212_;
v___y_1194_ = v___y_1211_;
v___y_1195_ = v_a_1242_;
v___y_1196_ = v_a_1232_;
v___y_1197_ = v_a_1214_;
v_a_1198_ = v_a_1252_;
goto v___jp_1191_;
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
lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec_ref(v___y_1213_);
v___x_1253_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22));
v___x_1254_ = l_Lake_JsonObject_getJson_x3f(v_a_1136_, v___x_1253_);
lean_dec(v_a_1136_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v___x_1255_; 
lean_dec_ref(v_a_1214_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
v___x_1255_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__11));
v_a_1157_ = v___x_1255_;
goto v___jp_1156_;
}
else
{
lean_object* v_val_1256_; lean_object* v___x_1257_; 
v_val_1256_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_val_1256_);
lean_dec_ref(v___x_1254_);
v___x_1257_ = l_Lean_Json_getStr_x3f(v_val_1256_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec_ref(v_a_1214_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_a_1258_);
lean_dec_ref(v___x_1257_);
v___x_1259_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__12));
v___x_1260_ = lean_string_append(v___x_1259_, v_a_1258_);
lean_dec(v_a_1258_);
v_a_1157_ = v___x_1260_;
goto v___jp_1156_;
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
lean_del_object(v___x_1154_);
v_a_1261_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1257_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1257_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set_tag(v___x_1263_, 0);
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
v___y_1169_ = v___y_1210_;
v___y_1170_ = v___y_1212_;
v___y_1171_ = v___y_1211_;
v___y_1172_ = v_a_1214_;
v_a_1173_ = v___x_1266_;
goto v___jp_1168_;
}
}
}
}
}
}
v___jp_1269_:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lake_defaultManifestFile;
v___y_1210_ = v___y_1270_;
v___y_1211_ = v___y_1272_;
v___y_1212_ = v___y_1271_;
v___y_1213_ = v___y_1273_;
v_a_1214_ = v___x_1274_;
goto v___jp_1209_;
}
v___jp_1275_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__2));
v___x_1281_ = l_Lake_JsonObject_getJson_x3f(v_a_1136_, v___x_1280_);
if (lean_obj_tag(v___x_1281_) == 0)
{
v___y_1270_ = v_a_1279_;
v___y_1271_ = v___y_1276_;
v___y_1272_ = v___y_1277_;
v___y_1273_ = v___y_1278_;
goto v___jp_1269_;
}
else
{
lean_object* v_val_1282_; lean_object* v___x_1283_; 
v_val_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_val_1282_);
lean_dec_ref(v___x_1281_);
v___x_1283_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1282_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
lean_dec_ref(v_a_1279_);
lean_dec_ref(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref(v___x_1283_);
v___x_1285_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__13));
v___x_1286_ = lean_string_append(v___x_1285_, v_a_1284_);
lean_dec(v_a_1284_);
v_a_1157_ = v___x_1286_;
goto v___jp_1156_;
}
else
{
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1287_; 
lean_dec_ref(v_a_1279_);
lean_dec_ref(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v_a_1287_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1287_);
lean_dec_ref(v___x_1283_);
v_a_1157_ = v_a_1287_;
goto v___jp_1156_;
}
else
{
lean_object* v_a_1288_; 
v_a_1288_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1288_);
lean_dec_ref(v___x_1283_);
if (lean_obj_tag(v_a_1288_) == 0)
{
v___y_1270_ = v_a_1279_;
v___y_1271_ = v___y_1276_;
v___y_1272_ = v___y_1277_;
v___y_1273_ = v___y_1278_;
goto v___jp_1269_;
}
else
{
lean_object* v_val_1289_; 
v_val_1289_ = lean_ctor_get(v_a_1288_, 0);
lean_inc(v_val_1289_);
lean_dec_ref(v_a_1288_);
v___y_1210_ = v_a_1279_;
v___y_1211_ = v___y_1277_;
v___y_1212_ = v___y_1276_;
v___y_1213_ = v___y_1278_;
v_a_1214_ = v_val_1289_;
goto v___jp_1209_;
}
}
}
}
}
v___jp_1290_:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Lake_defaultConfigFile;
v___y_1276_ = v___y_1292_;
v___y_1277_ = v___y_1291_;
v___y_1278_ = v___y_1293_;
v_a_1279_ = v___x_1294_;
goto v___jp_1275_;
}
v___jp_1295_:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__3));
v___x_1298_ = l_Lake_JsonObject_getJson_x3f(v_a_1136_, v___x_1297_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v___x_1299_; 
lean_dec_ref(v_a_1296_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v___x_1299_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__14));
v_a_1157_ = v___x_1299_;
goto v___jp_1156_;
}
else
{
lean_object* v_val_1300_; lean_object* v___x_1301_; 
v_val_1300_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_val_1300_);
lean_dec_ref(v___x_1298_);
v___x_1301_ = l_Lean_Json_getStr_x3f(v_val_1300_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
lean_dec_ref(v_a_1296_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1302_);
lean_dec_ref(v___x_1301_);
v___x_1303_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__15));
v___x_1304_ = lean_string_append(v___x_1303_, v_a_1302_);
lean_dec(v_a_1302_);
v_a_1157_ = v___x_1304_;
goto v___jp_1156_;
}
else
{
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1305_; 
lean_dec_ref(v_a_1296_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v_a_1305_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1305_);
lean_dec_ref(v___x_1301_);
v_a_1157_ = v_a_1305_;
goto v___jp_1156_;
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v_a_1306_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1306_);
lean_dec_ref(v___x_1301_);
v___x_1307_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10));
v___x_1308_ = l_Lake_JsonObject_getJson_x3f(v_a_1136_, v___x_1307_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v___x_1309_; 
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1296_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v___x_1309_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__16));
v_a_1157_ = v___x_1309_;
goto v___jp_1156_;
}
else
{
lean_object* v_val_1310_; lean_object* v___x_1311_; 
v_val_1310_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_val_1310_);
lean_dec_ref(v___x_1308_);
v___x_1311_ = l_Lean_Json_getBool_x3f(v_val_1310_);
lean_dec(v_val_1310_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1296_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec_ref(v___x_1311_);
v___x_1313_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__17));
v___x_1314_ = lean_string_append(v___x_1313_, v_a_1312_);
lean_dec(v_a_1312_);
v_a_1157_ = v___x_1314_;
goto v___jp_1156_;
}
else
{
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1315_; 
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1296_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v_a_1315_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1315_);
lean_dec_ref(v___x_1311_);
v_a_1157_ = v_a_1315_;
goto v___jp_1156_;
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v_a_1316_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1316_);
lean_dec_ref(v___x_1311_);
v___x_1317_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__1));
v___x_1318_ = l_Lake_JsonObject_getJson_x3f(v_a_1136_, v___x_1317_);
if (lean_obj_tag(v___x_1318_) == 0)
{
uint8_t v___x_1319_; 
v___x_1319_ = lean_unbox(v_a_1316_);
lean_dec(v_a_1316_);
v___y_1291_ = v_a_1296_;
v___y_1292_ = v___x_1319_;
v___y_1293_ = v_a_1306_;
goto v___jp_1290_;
}
else
{
lean_object* v_val_1320_; lean_object* v___x_1321_; 
v_val_1320_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_val_1320_);
lean_dec_ref(v___x_1318_);
v___x_1321_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1320_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_dec(v_a_1316_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1296_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1322_);
lean_dec_ref(v___x_1321_);
v___x_1323_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__18));
v___x_1324_ = lean_string_append(v___x_1323_, v_a_1322_);
lean_dec(v_a_1322_);
v_a_1157_ = v___x_1324_;
goto v___jp_1156_;
}
else
{
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1325_; 
lean_dec(v_a_1316_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1296_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1138_);
lean_dec(v_a_1136_);
v_a_1325_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1325_);
lean_dec_ref(v___x_1321_);
v_a_1157_ = v_a_1325_;
goto v___jp_1156_;
}
else
{
lean_object* v_a_1326_; 
v_a_1326_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1326_);
lean_dec_ref(v___x_1321_);
if (lean_obj_tag(v_a_1326_) == 0)
{
uint8_t v___x_1327_; 
v___x_1327_ = lean_unbox(v_a_1316_);
lean_dec(v_a_1316_);
v___y_1291_ = v_a_1296_;
v___y_1292_ = v___x_1327_;
v___y_1293_ = v_a_1306_;
goto v___jp_1290_;
}
else
{
lean_object* v_val_1328_; uint8_t v___x_1329_; 
v_val_1328_ = lean_ctor_get(v_a_1326_, 0);
lean_inc(v_val_1328_);
lean_dec_ref(v_a_1326_);
v___x_1329_ = lean_unbox(v_a_1316_);
lean_dec(v_a_1316_);
v___y_1276_ = v___x_1329_;
v___y_1277_ = v_a_1296_;
v___y_1278_ = v_a_1306_;
v_a_1279_ = v_val_1328_;
goto v___jp_1275_;
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
v___jp_1330_:
{
lean_object* v___x_1331_; 
v___x_1331_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v_a_1296_ = v___x_1331_;
goto v___jp_1295_;
}
}
}
}
}
}
}
}
}
v___jp_1114_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_a_1115_);
lean_dec_ref(v_a_1115_);
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
return v___x_1117_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setInherited(lean_object* v_entry_1361_){
_start:
{
lean_object* v_name_1362_; lean_object* v_scope_1363_; lean_object* v_configFile_1364_; lean_object* v_manifestFile_x3f_1365_; lean_object* v_src_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1374_; 
v_name_1362_ = lean_ctor_get(v_entry_1361_, 0);
v_scope_1363_ = lean_ctor_get(v_entry_1361_, 1);
v_configFile_1364_ = lean_ctor_get(v_entry_1361_, 2);
v_manifestFile_x3f_1365_ = lean_ctor_get(v_entry_1361_, 3);
v_src_1366_ = lean_ctor_get(v_entry_1361_, 4);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_entry_1361_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1368_ = v_entry_1361_;
v_isShared_1369_ = v_isSharedCheck_1374_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_src_1366_);
lean_inc(v_manifestFile_x3f_1365_);
lean_inc(v_configFile_1364_);
lean_inc(v_scope_1363_);
lean_inc(v_name_1362_);
lean_dec(v_entry_1361_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1374_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
uint8_t v___x_1370_; lean_object* v___x_1372_; 
v___x_1370_ = 1;
if (v_isShared_1369_ == 0)
{
v___x_1372_ = v___x_1368_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_name_1362_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_scope_1363_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_configFile_1364_);
lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_manifestFile_x3f_1365_);
lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_src_1366_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*5, v___x_1370_);
return v___x_1372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setConfigFile(lean_object* v_path_1375_, lean_object* v_entry_1376_){
_start:
{
lean_object* v_name_1377_; lean_object* v_scope_1378_; uint8_t v_inherited_1379_; lean_object* v_manifestFile_x3f_1380_; lean_object* v_src_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
v_name_1377_ = lean_ctor_get(v_entry_1376_, 0);
v_scope_1378_ = lean_ctor_get(v_entry_1376_, 1);
v_inherited_1379_ = lean_ctor_get_uint8(v_entry_1376_, sizeof(void*)*5);
v_manifestFile_x3f_1380_ = lean_ctor_get(v_entry_1376_, 3);
v_src_1381_ = lean_ctor_get(v_entry_1376_, 4);
v_isSharedCheck_1388_ = !lean_is_exclusive(v_entry_1376_);
if (v_isSharedCheck_1388_ == 0)
{
lean_object* v_unused_1389_; 
v_unused_1389_ = lean_ctor_get(v_entry_1376_, 2);
lean_dec(v_unused_1389_);
v___x_1383_ = v_entry_1376_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_src_1381_);
lean_inc(v_manifestFile_x3f_1380_);
lean_inc(v_scope_1378_);
lean_inc(v_name_1377_);
lean_dec(v_entry_1376_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 2, v_path_1375_);
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_name_1377_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v_scope_1378_);
lean_ctor_set(v_reuseFailAlloc_1387_, 2, v_path_1375_);
lean_ctor_set(v_reuseFailAlloc_1387_, 3, v_manifestFile_x3f_1380_);
lean_ctor_set(v_reuseFailAlloc_1387_, 4, v_src_1381_);
lean_ctor_set_uint8(v_reuseFailAlloc_1387_, sizeof(void*)*5, v_inherited_1379_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setManifestFile(lean_object* v_path_x3f_1390_, lean_object* v_entry_1391_){
_start:
{
lean_object* v_name_1392_; lean_object* v_scope_1393_; uint8_t v_inherited_1394_; lean_object* v_configFile_1395_; lean_object* v_src_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
v_name_1392_ = lean_ctor_get(v_entry_1391_, 0);
v_scope_1393_ = lean_ctor_get(v_entry_1391_, 1);
v_inherited_1394_ = lean_ctor_get_uint8(v_entry_1391_, sizeof(void*)*5);
v_configFile_1395_ = lean_ctor_get(v_entry_1391_, 2);
v_src_1396_ = lean_ctor_get(v_entry_1391_, 4);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_entry_1391_);
if (v_isSharedCheck_1403_ == 0)
{
lean_object* v_unused_1404_; 
v_unused_1404_ = lean_ctor_get(v_entry_1391_, 3);
lean_dec(v_unused_1404_);
v___x_1398_ = v_entry_1391_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_src_1396_);
lean_inc(v_configFile_1395_);
lean_inc(v_scope_1393_);
lean_inc(v_name_1392_);
lean_dec(v_entry_1391_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 3, v_path_x3f_1390_);
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_name_1392_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_scope_1393_);
lean_ctor_set(v_reuseFailAlloc_1402_, 2, v_configFile_1395_);
lean_ctor_set(v_reuseFailAlloc_1402_, 3, v_path_x3f_1390_);
lean_ctor_set(v_reuseFailAlloc_1402_, 4, v_src_1396_);
lean_ctor_set_uint8(v_reuseFailAlloc_1402_, sizeof(void*)*5, v_inherited_1394_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_inDirectory(lean_object* v_pkgDir_1405_, lean_object* v_entry_1406_){
_start:
{
lean_object* v_src_1407_; 
v_src_1407_ = lean_ctor_get(v_entry_1406_, 4);
lean_inc_ref(v_src_1407_);
if (lean_obj_tag(v_src_1407_) == 0)
{
lean_object* v_name_1408_; lean_object* v_scope_1409_; uint8_t v_inherited_1410_; lean_object* v_configFile_1411_; lean_object* v_manifestFile_x3f_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1428_; 
v_name_1408_ = lean_ctor_get(v_entry_1406_, 0);
v_scope_1409_ = lean_ctor_get(v_entry_1406_, 1);
v_inherited_1410_ = lean_ctor_get_uint8(v_entry_1406_, sizeof(void*)*5);
v_configFile_1411_ = lean_ctor_get(v_entry_1406_, 2);
v_manifestFile_x3f_1412_ = lean_ctor_get(v_entry_1406_, 3);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_entry_1406_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; 
v_unused_1429_ = lean_ctor_get(v_entry_1406_, 4);
lean_dec(v_unused_1429_);
v___x_1414_ = v_entry_1406_;
v_isShared_1415_ = v_isSharedCheck_1428_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_manifestFile_x3f_1412_);
lean_inc(v_configFile_1411_);
lean_inc(v_scope_1409_);
lean_inc(v_name_1408_);
lean_dec(v_entry_1406_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1428_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v_dir_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1427_; 
v_dir_1416_ = lean_ctor_get(v_src_1407_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_src_1407_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1418_ = v_src_1407_;
v_isShared_1419_ = v_isSharedCheck_1427_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_dir_1416_);
lean_dec(v_src_1407_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1427_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1420_ = l_Lake_joinRelative(v_pkgDir_1405_, v_dir_1416_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1420_);
v___x_1422_ = v___x_1418_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1424_; 
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 4, v___x_1422_);
v___x_1424_ = v___x_1414_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_name_1408_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_scope_1409_);
lean_ctor_set(v_reuseFailAlloc_1425_, 2, v_configFile_1411_);
lean_ctor_set(v_reuseFailAlloc_1425_, 3, v_manifestFile_x3f_1412_);
lean_ctor_set(v_reuseFailAlloc_1425_, 4, v___x_1422_);
lean_ctor_set_uint8(v_reuseFailAlloc_1425_, sizeof(void*)*5, v_inherited_1410_);
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
else
{
lean_dec_ref(v_src_1407_);
lean_dec_ref(v_pkgDir_1405_);
return v_entry_1406_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(lean_object* v_x_1430_){
_start:
{
if (lean_obj_tag(v_x_1430_) == 0)
{
lean_object* v_name_1431_; uint8_t v_inherited_1432_; lean_object* v_dir_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v_name_1431_ = lean_ctor_get(v_x_1430_, 0);
v_inherited_1432_ = lean_ctor_get_uint8(v_x_1430_, sizeof(void*)*3);
v_dir_1433_ = lean_ctor_get(v_x_1430_, 2);
v___x_1434_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_1435_ = l_Lake_defaultConfigFile;
v___x_1436_ = lean_box(0);
lean_inc_ref(v_dir_1433_);
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v_dir_1433_);
lean_inc(v_name_1431_);
v___x_1438_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1438_, 0, v_name_1431_);
lean_ctor_set(v___x_1438_, 1, v___x_1434_);
lean_ctor_set(v___x_1438_, 2, v___x_1435_);
lean_ctor_set(v___x_1438_, 3, v___x_1436_);
lean_ctor_set(v___x_1438_, 4, v___x_1437_);
lean_ctor_set_uint8(v___x_1438_, sizeof(void*)*5, v_inherited_1432_);
return v___x_1438_;
}
else
{
lean_object* v_name_1439_; uint8_t v_inherited_1440_; lean_object* v_url_1441_; lean_object* v_rev_1442_; lean_object* v_inputRev_x3f_1443_; lean_object* v_subDir_x3f_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v_name_1439_ = lean_ctor_get(v_x_1430_, 0);
v_inherited_1440_ = lean_ctor_get_uint8(v_x_1430_, sizeof(void*)*6);
v_url_1441_ = lean_ctor_get(v_x_1430_, 2);
v_rev_1442_ = lean_ctor_get(v_x_1430_, 3);
v_inputRev_x3f_1443_ = lean_ctor_get(v_x_1430_, 4);
v_subDir_x3f_1444_ = lean_ctor_get(v_x_1430_, 5);
v___x_1445_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_1446_ = l_Lake_defaultConfigFile;
v___x_1447_ = lean_box(0);
lean_inc(v_subDir_x3f_1444_);
lean_inc(v_inputRev_x3f_1443_);
lean_inc_ref(v_rev_1442_);
lean_inc_ref(v_url_1441_);
v___x_1448_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1448_, 0, v_url_1441_);
lean_ctor_set(v___x_1448_, 1, v_rev_1442_);
lean_ctor_set(v___x_1448_, 2, v_inputRev_x3f_1443_);
lean_ctor_set(v___x_1448_, 3, v_subDir_x3f_1444_);
lean_inc(v_name_1439_);
v___x_1449_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1449_, 0, v_name_1439_);
lean_ctor_set(v___x_1449_, 1, v___x_1445_);
lean_ctor_set(v___x_1449_, 2, v___x_1446_);
lean_ctor_set(v___x_1449_, 3, v___x_1447_);
lean_ctor_set(v___x_1449_, 4, v___x_1448_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*5, v_inherited_1440_);
return v___x_1449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6___boxed(lean_object* v_x_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(v_x_1450_);
lean_dec_ref(v_x_1450_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_addPackage(lean_object* v_entry_1452_, lean_object* v_self_1453_){
_start:
{
lean_object* v_name_1454_; lean_object* v_lakeDir_1455_; uint8_t v_fixedToolchain_1456_; lean_object* v_packagesDir_x3f_1457_; lean_object* v_packages_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1466_; 
v_name_1454_ = lean_ctor_get(v_self_1453_, 0);
v_lakeDir_1455_ = lean_ctor_get(v_self_1453_, 1);
v_fixedToolchain_1456_ = lean_ctor_get_uint8(v_self_1453_, sizeof(void*)*4);
v_packagesDir_x3f_1457_ = lean_ctor_get(v_self_1453_, 2);
v_packages_1458_ = lean_ctor_get(v_self_1453_, 3);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_self_1453_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1460_ = v_self_1453_;
v_isShared_1461_ = v_isSharedCheck_1466_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_packages_1458_);
lean_inc(v_packagesDir_x3f_1457_);
lean_inc(v_lakeDir_1455_);
lean_inc(v_name_1454_);
lean_dec(v_self_1453_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1466_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1462_ = lean_array_push(v_packages_1458_, v_entry_1452_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 3, v___x_1462_);
v___x_1464_ = v___x_1460_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_name_1454_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_lakeDir_1455_);
lean_ctor_set(v_reuseFailAlloc_1465_, 2, v_packagesDir_x3f_1457_);
lean_ctor_set(v_reuseFailAlloc_1465_, 3, v___x_1462_);
lean_ctor_set_uint8(v_reuseFailAlloc_1465_, sizeof(void*)*4, v_fixedToolchain_1456_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(size_t v_sz_1467_, size_t v_i_1468_, lean_object* v_bs_1469_){
_start:
{
uint8_t v___x_1470_; 
v___x_1470_ = lean_usize_dec_lt(v_i_1468_, v_sz_1467_);
if (v___x_1470_ == 0)
{
return v_bs_1469_;
}
else
{
lean_object* v_v_1471_; lean_object* v___x_1472_; lean_object* v_bs_x27_1473_; lean_object* v___x_1474_; size_t v___x_1475_; size_t v___x_1476_; lean_object* v___x_1477_; 
v_v_1471_ = lean_array_uget(v_bs_1469_, v_i_1468_);
v___x_1472_ = lean_unsigned_to_nat(0u);
v_bs_x27_1473_ = lean_array_uset(v_bs_1469_, v_i_1468_, v___x_1472_);
v___x_1474_ = l_Lake_PackageEntry_toJson(v_v_1471_);
v___x_1475_ = ((size_t)1ULL);
v___x_1476_ = lean_usize_add(v_i_1468_, v___x_1475_);
v___x_1477_ = lean_array_uset(v_bs_x27_1473_, v_i_1468_, v___x_1474_);
v_i_1468_ = v___x_1476_;
v_bs_1469_ = v___x_1477_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1479_, lean_object* v_i_1480_, lean_object* v_bs_1481_){
_start:
{
size_t v_sz_boxed_1482_; size_t v_i_boxed_1483_; lean_object* v_res_1484_; 
v_sz_boxed_1482_ = lean_unbox_usize(v_sz_1479_);
lean_dec(v_sz_1479_);
v_i_boxed_1483_ = lean_unbox_usize(v_i_1480_);
lean_dec(v_i_1480_);
v_res_1484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(v_sz_boxed_1482_, v_i_boxed_1483_, v_bs_1481_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_Manifest_toJson_spec__0(lean_object* v_a_1485_){
_start:
{
size_t v_sz_1486_; size_t v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v_sz_1486_ = lean_array_size(v_a_1485_);
v___x_1487_ = ((size_t)0ULL);
v___x_1488_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(v_sz_1486_, v___x_1487_, v_a_1485_);
v___x_1489_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
return v___x_1489_;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__1(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = ((lean_object*)(l_Lake_Manifest_version___closed__2));
v___x_1492_ = l_Lake_StdVer_toString(v___x_1491_);
return v___x_1492_;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__2(void){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__1, &l_Lake_Manifest_toJson___closed__1_once, _init_l_Lake_Manifest_toJson___closed__1);
v___x_1494_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
return v___x_1494_;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__3(void){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1495_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__2, &l_Lake_Manifest_toJson___closed__2_once, _init_l_Lake_Manifest_toJson___closed__2);
v___x_1496_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__0));
v___x_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
lean_ctor_set(v___x_1497_, 1, v___x_1495_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_toJson(lean_object* v_self_1502_){
_start:
{
lean_object* v_name_1503_; lean_object* v_lakeDir_1504_; uint8_t v_fixedToolchain_1505_; lean_object* v_packagesDir_x3f_1506_; lean_object* v_packages_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v_name_1503_ = lean_ctor_get(v_self_1502_, 0);
lean_inc(v_name_1503_);
v_lakeDir_1504_ = lean_ctor_get(v_self_1502_, 1);
lean_inc_ref(v_lakeDir_1504_);
v_fixedToolchain_1505_ = lean_ctor_get_uint8(v_self_1502_, sizeof(void*)*4);
v_packagesDir_x3f_1506_ = lean_ctor_get(v_self_1502_, 2);
lean_inc(v_packagesDir_x3f_1506_);
v_packages_1507_ = lean_ctor_get(v_self_1502_, 3);
lean_inc_ref(v_packages_1507_);
lean_dec_ref(v_self_1502_);
v___x_1508_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__3, &l_Lake_Manifest_toJson___closed__3_once, _init_l_Lake_Manifest_toJson___closed__3);
v___x_1509_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__4));
v___x_1510_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1510_, 0, v_fixedToolchain_1505_);
v___x_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1509_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
v___x_1512_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_1513_ = 1;
v___x_1514_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1503_, v___x_1513_);
v___x_1515_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
v___x_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1512_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
v___x_1517_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__5));
v___x_1518_ = l_Lake_mkRelPathString(v_lakeDir_1504_);
v___x_1519_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
v___x_1520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1517_);
lean_ctor_set(v___x_1520_, 1, v___x_1519_);
v___x_1521_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__6));
v___x_1522_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_packagesDir_x3f_1506_);
v___x_1523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1521_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___x_1524_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__7));
v___x_1525_ = l_Array_toJson___at___00Lake_Manifest_toJson_spec__0(v_packages_1507_);
v___x_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = lean_box(0);
v___x_1528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1526_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1523_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1520_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
v___x_1531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1516_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1511_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1508_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = l_Lean_Json_mkObj(v___x_1533_);
return v___x_1534_;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6(void){
_start:
{
lean_object* v_natZero_1545_; lean_object* v_intZero_1546_; 
v_natZero_1545_ = lean_unsigned_to_nat(0u);
v_intZero_1546_ = lean_nat_to_int(v_natZero_1545_);
return v_intZero_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(lean_object* v_obj_1552_){
_start:
{
lean_object* v___y_1554_; lean_object* v_ver_1562_; lean_object* v_major_1563_; lean_object* v_ver_1580_; lean_object* v_a_1589_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__0));
v___x_1616_ = l_Lake_JsonObject_getJson_x3f(v_obj_1552_, v___x_1615_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8));
v___x_1618_ = l_Lake_JsonObject_getJson_x3f(v_obj_1552_, v___x_1617_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v___x_1619_; 
v___x_1619_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__10));
return v___x_1619_;
}
else
{
lean_object* v_val_1620_; 
v_val_1620_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_val_1620_);
lean_dec_ref(v___x_1618_);
v_a_1589_ = v_val_1620_;
goto v___jp_1588_;
}
}
else
{
lean_object* v_val_1621_; 
v_val_1621_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_val_1621_);
lean_dec_ref(v___x_1616_);
v_a_1589_ = v_val_1621_;
goto v___jp_1588_;
}
v___jp_1553_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1555_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__0));
v___x_1556_ = l_Lake_SemVerCore_toString(v___y_1554_);
v___x_1557_ = lean_string_append(v___x_1555_, v___x_1556_);
lean_dec_ref(v___x_1556_);
v___x_1558_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1559_ = lean_string_append(v___x_1557_, v___x_1558_);
v___x_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
return v___x_1560_;
}
v___jp_1561_:
{
lean_object* v___x_1564_; uint8_t v___x_1565_; 
v___x_1564_ = lean_unsigned_to_nat(1u);
v___x_1565_ = lean_nat_dec_lt(v___x_1564_, v_major_1563_);
lean_dec(v_major_1563_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__1));
v___x_1567_ = l_Lake_instOrdSemVerCore_ord(v_ver_1562_, v___x_1566_);
if (v___x_1567_ == 0)
{
v___y_1554_ = v_ver_1562_;
goto v___jp_1553_;
}
else
{
if (v___x_1565_ == 0)
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1568_, 0, v_ver_1562_);
return v___x_1568_;
}
else
{
v___y_1554_ = v_ver_1562_;
goto v___jp_1553_;
}
}
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1569_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__2));
v___x_1570_ = l_Lake_SemVerCore_toString(v_ver_1562_);
v___x_1571_ = lean_string_append(v___x_1569_, v___x_1570_);
lean_dec_ref(v___x_1570_);
v___x_1572_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__3));
v___x_1573_ = lean_string_append(v___x_1571_, v___x_1572_);
v___x_1574_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__1, &l_Lake_Manifest_toJson___closed__1_once, _init_l_Lake_Manifest_toJson___closed__1);
v___x_1575_ = lean_string_append(v___x_1573_, v___x_1574_);
v___x_1576_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4));
v___x_1577_ = lean_string_append(v___x_1575_, v___x_1576_);
v___x_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
return v___x_1578_;
}
}
v___jp_1579_:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1581_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__5));
v___x_1582_ = lean_unsigned_to_nat(80u);
v___x_1583_ = l_Lean_Json_pretty(v_ver_1580_, v___x_1582_);
v___x_1584_ = lean_string_append(v___x_1581_, v___x_1583_);
lean_dec_ref(v___x_1583_);
v___x_1585_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4));
v___x_1586_ = lean_string_append(v___x_1584_, v___x_1585_);
v___x_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
return v___x_1587_;
}
v___jp_1588_:
{
switch(lean_obj_tag(v_a_1589_))
{
case 2:
{
lean_object* v_n_1590_; lean_object* v_mantissa_1591_; lean_object* v_exponent_1592_; lean_object* v_natZero_1593_; lean_object* v_intZero_1594_; uint8_t v_isNeg_1595_; 
v_n_1590_ = lean_ctor_get(v_a_1589_, 0);
v_mantissa_1591_ = lean_ctor_get(v_n_1590_, 0);
v_exponent_1592_ = lean_ctor_get(v_n_1590_, 1);
v_natZero_1593_ = lean_unsigned_to_nat(0u);
v_intZero_1594_ = lean_obj_once(&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6, &l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6_once, _init_l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6);
v_isNeg_1595_ = lean_int_dec_lt(v_mantissa_1591_, v_intZero_1594_);
if (v_isNeg_1595_ == 0)
{
uint8_t v___x_1596_; 
v___x_1596_ = lean_nat_dec_eq(v_exponent_1592_, v_natZero_1593_);
if (v___x_1596_ == 0)
{
v_ver_1580_ = v_a_1589_;
goto v___jp_1579_;
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1598_; 
lean_inc(v_mantissa_1591_);
lean_dec_ref(v_a_1589_);
v_a_1597_ = lean_nat_abs(v_mantissa_1591_);
lean_dec(v_mantissa_1591_);
v___x_1598_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1598_, 0, v_natZero_1593_);
lean_ctor_set(v___x_1598_, 1, v_a_1597_);
lean_ctor_set(v___x_1598_, 2, v_natZero_1593_);
v_ver_1562_ = v___x_1598_;
v_major_1563_ = v_natZero_1593_;
goto v___jp_1561_;
}
}
else
{
v_ver_1580_ = v_a_1589_;
goto v___jp_1579_;
}
}
case 3:
{
lean_object* v_s_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v_s_1599_ = lean_ctor_get(v_a_1589_, 0);
lean_inc_ref(v_s_1599_);
lean_dec_ref(v_a_1589_);
v___x_1600_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7));
v___x_1601_ = lean_unsigned_to_nat(0u);
v___x_1602_ = lean_string_utf8_byte_size(v_s_1599_);
v___x_1603_ = l___private_Lake_Util_Version_0__Lake_runVerParse(lean_box(0), v_s_1599_, v___x_1600_, v___x_1601_, v___x_1602_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
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
lean_object* v_a_1612_; lean_object* v_toSemVerCore_1613_; lean_object* v_major_1614_; 
v_a_1612_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1612_);
lean_dec_ref(v___x_1603_);
v_toSemVerCore_1613_ = lean_ctor_get(v_a_1612_, 0);
lean_inc_ref(v_toSemVerCore_1613_);
lean_dec(v_a_1612_);
v_major_1614_ = lean_ctor_get(v_toSemVerCore_1613_, 0);
lean_inc(v_major_1614_);
v_ver_1562_ = v_toSemVerCore_1613_;
v_major_1563_ = v_major_1614_;
goto v___jp_1561_;
}
}
default: 
{
v_ver_1580_ = v_a_1589_;
goto v___jp_1579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___boxed(lean_object* v_obj_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_obj_1622_);
lean_dec(v_obj_1622_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(size_t v_sz_1624_, size_t v_i_1625_, lean_object* v_bs_1626_){
_start:
{
uint8_t v___x_1627_; 
v___x_1627_ = lean_usize_dec_lt(v_i_1625_, v_sz_1624_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; 
v___x_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1628_, 0, v_bs_1626_);
return v___x_1628_;
}
else
{
lean_object* v_v_1629_; lean_object* v___x_1630_; 
v_v_1629_ = lean_array_uget_borrowed(v_bs_1626_, v_i_1625_);
lean_inc(v_v_1629_);
v___x_1630_ = l_Lake_PackageEntry_fromJson_x3f(v_v_1629_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec_ref(v_bs_1626_);
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1630_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1630_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1640_; lean_object* v_bs_x27_1641_; size_t v___x_1642_; size_t v___x_1643_; lean_object* v___x_1644_; 
v_a_1639_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1639_);
lean_dec_ref(v___x_1630_);
v___x_1640_ = lean_unsigned_to_nat(0u);
v_bs_x27_1641_ = lean_array_uset(v_bs_1626_, v_i_1625_, v___x_1640_);
v___x_1642_ = ((size_t)1ULL);
v___x_1643_ = lean_usize_add(v_i_1625_, v___x_1642_);
v___x_1644_ = lean_array_uset(v_bs_x27_1641_, v_i_1625_, v_a_1639_);
v_i_1625_ = v___x_1643_;
v_bs_1626_ = v___x_1644_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_1646_, lean_object* v_i_1647_, lean_object* v_bs_1648_){
_start:
{
size_t v_sz_boxed_1649_; size_t v_i_boxed_1650_; lean_object* v_res_1651_; 
v_sz_boxed_1649_ = lean_unbox_usize(v_sz_1646_);
lean_dec(v_sz_1646_);
v_i_boxed_1650_ = lean_unbox_usize(v_i_1647_);
lean_dec(v_i_1647_);
v_res_1651_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(v_sz_boxed_1649_, v_i_boxed_1650_, v_bs_1648_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1(lean_object* v_x_1653_){
_start:
{
if (lean_obj_tag(v_x_1653_) == 4)
{
lean_object* v_elems_1654_; size_t v_sz_1655_; size_t v___x_1656_; lean_object* v___x_1657_; 
v_elems_1654_ = lean_ctor_get(v_x_1653_, 0);
lean_inc_ref(v_elems_1654_);
lean_dec_ref(v_x_1653_);
v_sz_1655_ = lean_array_size(v_elems_1654_);
v___x_1656_ = ((size_t)0ULL);
v___x_1657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(v_sz_1655_, v___x_1656_, v_elems_1654_);
return v___x_1657_;
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1658_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1___closed__0));
v___x_1659_ = lean_unsigned_to_nat(80u);
v___x_1660_ = l_Lean_Json_pretty(v_x_1653_, v___x_1659_);
v___x_1661_ = lean_string_append(v___x_1658_, v___x_1660_);
lean_dec_ref(v___x_1660_);
v___x_1662_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1663_ = lean_string_append(v___x_1661_, v___x_1662_);
v___x_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
return v___x_1664_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1(lean_object* v_x_1667_){
_start:
{
if (lean_obj_tag(v_x_1667_) == 0)
{
lean_object* v___x_1668_; 
v___x_1668_ = ((lean_object*)(l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1___closed__0));
return v___x_1668_;
}
else
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1(v_x_1667_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1669_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1686_; 
v_a_1678_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1680_ = v___x_1669_;
v_isShared_1681_ = v_isSharedCheck_1686_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1669_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1686_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v___x_1684_; 
v___x_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1682_, 0, v_a_1678_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1682_);
v___x_1684_ = v___x_1680_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1682_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(size_t v_sz_1687_, size_t v_i_1688_, lean_object* v_bs_1689_){
_start:
{
uint8_t v___x_1690_; 
v___x_1690_ = lean_usize_dec_lt(v_i_1688_, v_sz_1687_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1691_, 0, v_bs_1689_);
return v___x_1691_;
}
else
{
lean_object* v_v_1692_; lean_object* v___x_1693_; 
v_v_1692_ = lean_array_uget_borrowed(v_bs_1689_, v_i_1688_);
lean_inc(v_v_1692_);
v___x_1693_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson(v_v_1692_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec_ref(v_bs_1689_);
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1693_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1693_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1703_; lean_object* v_bs_x27_1704_; size_t v___x_1705_; size_t v___x_1706_; lean_object* v___x_1707_; 
v_a_1702_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1702_);
lean_dec_ref(v___x_1693_);
v___x_1703_ = lean_unsigned_to_nat(0u);
v_bs_x27_1704_ = lean_array_uset(v_bs_1689_, v_i_1688_, v___x_1703_);
v___x_1705_ = ((size_t)1ULL);
v___x_1706_ = lean_usize_add(v_i_1688_, v___x_1705_);
v___x_1707_ = lean_array_uset(v_bs_x27_1704_, v_i_1688_, v_a_1702_);
v_i_1688_ = v___x_1706_;
v_bs_1689_ = v___x_1707_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_1709_, lean_object* v_i_1710_, lean_object* v_bs_1711_){
_start:
{
size_t v_sz_boxed_1712_; size_t v_i_boxed_1713_; lean_object* v_res_1714_; 
v_sz_boxed_1712_ = lean_unbox_usize(v_sz_1709_);
lean_dec(v_sz_1709_);
v_i_boxed_1713_ = lean_unbox_usize(v_i_1710_);
lean_dec(v_i_1710_);
v_res_1714_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(v_sz_boxed_1712_, v_i_boxed_1713_, v_bs_1711_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3(lean_object* v_x_1715_){
_start:
{
if (lean_obj_tag(v_x_1715_) == 4)
{
lean_object* v_elems_1716_; size_t v_sz_1717_; size_t v___x_1718_; lean_object* v___x_1719_; 
v_elems_1716_ = lean_ctor_get(v_x_1715_, 0);
lean_inc_ref(v_elems_1716_);
lean_dec_ref(v_x_1715_);
v_sz_1717_ = lean_array_size(v_elems_1716_);
v___x_1718_ = ((size_t)0ULL);
v___x_1719_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(v_sz_1717_, v___x_1718_, v_elems_1716_);
return v___x_1719_;
}
else
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1720_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1___closed__0));
v___x_1721_ = lean_unsigned_to_nat(80u);
v___x_1722_ = l_Lean_Json_pretty(v_x_1715_, v___x_1721_);
v___x_1723_ = lean_string_append(v___x_1720_, v___x_1722_);
lean_dec_ref(v___x_1722_);
v___x_1724_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1725_ = lean_string_append(v___x_1723_, v___x_1724_);
v___x_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
return v___x_1726_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2(lean_object* v_x_1729_){
_start:
{
if (lean_obj_tag(v_x_1729_) == 0)
{
lean_object* v___x_1730_; 
v___x_1730_ = ((lean_object*)(l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2___closed__0));
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3(v_x_1729_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1731_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1731_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1748_; 
v_a_1740_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1742_ = v___x_1731_;
v_isShared_1743_ = v_isSharedCheck_1748_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1731_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1748_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; lean_object* v___x_1746_; 
v___x_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1744_, 0, v_a_1740_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v___x_1744_);
v___x_1746_ = v___x_1742_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1744_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(size_t v_sz_1749_, size_t v_i_1750_, lean_object* v_bs_1751_){
_start:
{
uint8_t v___x_1752_; 
v___x_1752_ = lean_usize_dec_lt(v_i_1750_, v_sz_1749_);
if (v___x_1752_ == 0)
{
return v_bs_1751_;
}
else
{
lean_object* v_v_1753_; lean_object* v___x_1754_; lean_object* v_bs_x27_1755_; lean_object* v___x_1756_; size_t v___x_1757_; size_t v___x_1758_; lean_object* v___x_1759_; 
v_v_1753_ = lean_array_uget(v_bs_1751_, v_i_1750_);
v___x_1754_ = lean_unsigned_to_nat(0u);
v_bs_x27_1755_ = lean_array_uset(v_bs_1751_, v_i_1750_, v___x_1754_);
v___x_1756_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(v_v_1753_);
lean_dec(v_v_1753_);
v___x_1757_ = ((size_t)1ULL);
v___x_1758_ = lean_usize_add(v_i_1750_, v___x_1757_);
v___x_1759_ = lean_array_uset(v_bs_x27_1755_, v_i_1750_, v___x_1756_);
v_i_1750_ = v___x_1758_;
v_bs_1751_ = v___x_1759_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0___boxed(lean_object* v_sz_1761_, lean_object* v_i_1762_, lean_object* v_bs_1763_){
_start:
{
size_t v_sz_boxed_1764_; size_t v_i_boxed_1765_; lean_object* v_res_1766_; 
v_sz_boxed_1764_ = lean_unbox_usize(v_sz_1761_);
lean_dec(v_sz_1761_);
v_i_boxed_1765_ = lean_unbox_usize(v_i_1762_);
lean_dec(v_i_1762_);
v_res_1766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(v_sz_boxed_1764_, v_i_boxed_1765_, v_bs_1763_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(lean_object* v_ver_1780_, lean_object* v_obj_1781_){
_start:
{
lean_object* v_a_1783_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__4));
v___x_1793_ = l_Lake_StdVer_compare(v_ver_1780_, v___x_1792_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__7));
v___x_1795_ = l_Lake_JsonObject_getJson_x3f(v_obj_1781_, v___x_1794_);
if (lean_obj_tag(v___x_1795_) == 0)
{
goto v___jp_1788_;
}
else
{
lean_object* v_val_1796_; lean_object* v___x_1797_; 
v_val_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_val_1796_);
lean_dec_ref(v___x_1795_);
v___x_1797_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2(v_val_1796_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1807_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1807_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1807_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1802_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5));
v___x_1803_ = lean_string_append(v___x_1802_, v_a_1798_);
lean_dec(v_a_1798_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1803_);
v___x_1805_ = v___x_1800_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
else
{
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
v_a_1808_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1797_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1797_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
lean_ctor_set_tag(v___x_1810_, 0);
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
else
{
lean_object* v_a_1816_; 
v_a_1816_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_a_1816_);
lean_dec_ref(v___x_1797_);
if (lean_obj_tag(v_a_1816_) == 0)
{
goto v___jp_1788_;
}
else
{
lean_object* v_val_1817_; 
v_val_1817_ = lean_ctor_get(v_a_1816_, 0);
lean_inc(v_val_1817_);
lean_dec_ref(v_a_1816_);
v_a_1783_ = v_val_1817_;
goto v___jp_1782_;
}
}
}
}
}
else
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__7));
v___x_1819_ = l_Lake_JsonObject_getJson_x3f(v_obj_1781_, v___x_1818_);
if (lean_obj_tag(v___x_1819_) == 0)
{
goto v___jp_1790_;
}
else
{
lean_object* v_val_1820_; lean_object* v___x_1821_; 
v_val_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_val_1820_);
lean_dec_ref(v___x_1819_);
v___x_1821_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1(v_val_1820_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1831_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1831_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1831_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___x_1826_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5));
v___x_1827_ = lean_string_append(v___x_1826_, v_a_1822_);
lean_dec(v_a_1822_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1827_);
v___x_1829_ = v___x_1824_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
else
{
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
v_a_1832_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1821_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1821_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set_tag(v___x_1834_, 0);
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1848_; 
v_a_1840_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1842_ = v___x_1821_;
v_isShared_1843_ = v_isSharedCheck_1848_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1821_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1848_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
if (lean_obj_tag(v_a_1840_) == 0)
{
lean_del_object(v___x_1842_);
goto v___jp_1790_;
}
else
{
lean_object* v_val_1844_; lean_object* v___x_1846_; 
v_val_1844_ = lean_ctor_get(v_a_1840_, 0);
lean_inc(v_val_1844_);
lean_dec_ref(v_a_1840_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v_val_1844_);
v___x_1846_ = v___x_1842_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_val_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
}
}
}
v___jp_1782_:
{
size_t v_sz_1784_; size_t v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v_sz_1784_ = lean_array_size(v_a_1783_);
v___x_1785_ = ((size_t)0ULL);
v___x_1786_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(v_sz_1784_, v___x_1785_, v_a_1783_);
v___x_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
return v___x_1787_;
}
v___jp_1788_:
{
lean_object* v___x_1789_; 
v___x_1789_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__0));
v_a_1783_ = v___x_1789_;
goto v___jp_1782_;
}
v___jp_1790_:
{
lean_object* v___x_1791_; 
v___x_1791_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__2));
return v___x_1791_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___boxed(lean_object* v_ver_1849_, lean_object* v_obj_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(v_ver_1849_, v_obj_1850_);
lean_dec(v_obj_1850_);
lean_dec_ref(v_ver_1849_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0(lean_object* v_x_1854_){
_start:
{
if (lean_obj_tag(v_x_1854_) == 0)
{
lean_object* v___x_1855_; 
v___x_1855_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0___closed__0));
return v___x_1855_;
}
else
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_Name_fromJson_x3f(v_x_1854_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1856_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1856_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1873_; 
v_a_1865_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1867_ = v___x_1856_;
v_isShared_1868_ = v_isSharedCheck_1873_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1856_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1873_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1869_; lean_object* v___x_1871_; 
v___x_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1869_, 0, v_a_1865_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v___x_1869_);
v___x_1871_ = v___x_1867_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1(lean_object* v_x_1876_){
_start:
{
if (lean_obj_tag(v_x_1876_) == 0)
{
lean_object* v___x_1877_; 
v___x_1877_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1___closed__0));
return v___x_1877_;
}
else
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_Json_getBool_x3f(v_x_1876_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1878_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1878_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
else
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1895_; 
v_a_1887_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1889_ = v___x_1878_;
v_isShared_1890_ = v_isSharedCheck_1895_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1878_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1895_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; lean_object* v___x_1893_; 
v___x_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1891_, 0, v_a_1887_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v___x_1891_);
v___x_1893_ = v___x_1889_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1___boxed(lean_object* v_x_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1(v_x_1896_);
lean_dec(v_x_1896_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_fromJson_x3f(lean_object* v_json_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Lean_Json_getObj_x3f(v_json_1901_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1902_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1902_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1912_; 
v_a_1911_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1911_);
lean_dec_ref(v___x_1902_);
v___x_1912_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_a_1911_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec(v_a_1911_);
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1912_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1912_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
else
{
lean_object* v_a_1921_; uint8_t v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v_a_1926_; uint8_t v___y_1948_; lean_object* v___y_1949_; lean_object* v_a_1950_; uint8_t v___y_1976_; lean_object* v___y_1977_; uint8_t v___y_1980_; lean_object* v_a_1981_; uint8_t v___y_2007_; uint8_t v_a_2010_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v_a_1921_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1921_);
lean_dec_ref(v___x_1912_);
v___x_2037_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__4));
v___x_2038_ = l_Lake_JsonObject_getJson_x3f(v_a_1911_, v___x_2037_);
if (lean_obj_tag(v___x_2038_) == 0)
{
goto v___jp_2035_;
}
else
{
lean_object* v_val_2039_; lean_object* v___x_2040_; 
v_val_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_val_2039_);
lean_dec_ref(v___x_2038_);
v___x_2040_ = l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1(v_val_2039_);
lean_dec(v_val_2039_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2050_; 
lean_dec(v_a_1921_);
lean_dec(v_a_1911_);
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2050_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2050_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2045_ = ((lean_object*)(l_Lake_Manifest_fromJson_x3f___closed__2));
v___x_2046_ = lean_string_append(v___x_2045_, v_a_2041_);
lean_dec(v_a_2041_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v___x_2046_);
v___x_2048_ = v___x_2043_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
else
{
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v_a_1921_);
lean_dec(v_a_1911_);
v_a_2051_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2040_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2040_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
lean_ctor_set_tag(v___x_2053_, 0);
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
else
{
lean_object* v_a_2059_; 
v_a_2059_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2059_);
lean_dec_ref(v___x_2040_);
if (lean_obj_tag(v_a_2059_) == 0)
{
goto v___jp_2035_;
}
else
{
lean_object* v_val_2060_; uint8_t v___x_2061_; 
v_val_2060_ = lean_ctor_get(v_a_2059_, 0);
lean_inc(v_val_2060_);
lean_dec_ref(v_a_2059_);
v___x_2061_ = lean_unbox(v_val_2060_);
lean_dec(v_val_2060_);
v_a_2010_ = v___x_2061_;
goto v___jp_2009_;
}
}
}
}
v___jp_1922_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1927_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v_a_1921_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
v___x_1929_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(v___x_1928_, v_a_1911_);
lean_dec(v_a_1911_);
lean_dec_ref(v___x_1928_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec(v_a_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1929_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1929_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1946_; 
v_a_1938_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1940_ = v___x_1929_;
v_isShared_1941_ = v_isSharedCheck_1946_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1929_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1946_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1942_; lean_object* v___x_1944_; 
v___x_1942_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1942_, 0, v___y_1924_);
lean_ctor_set(v___x_1942_, 1, v___y_1925_);
lean_ctor_set(v___x_1942_, 2, v_a_1926_);
lean_ctor_set(v___x_1942_, 3, v_a_1938_);
lean_ctor_set_uint8(v___x_1942_, sizeof(void*)*4, v___y_1923_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v___x_1942_);
v___x_1944_ = v___x_1940_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
v___jp_1947_:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__6));
v___x_1952_ = l_Lake_JsonObject_getJson_x3f(v_a_1911_, v___x_1951_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v___x_1953_; 
v___x_1953_ = lean_box(0);
v___y_1923_ = v___y_1948_;
v___y_1924_ = v___y_1949_;
v___y_1925_ = v_a_1950_;
v_a_1926_ = v___x_1953_;
goto v___jp_1922_;
}
else
{
lean_object* v_val_1954_; lean_object* v___x_1955_; 
v_val_1954_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_val_1954_);
lean_dec_ref(v___x_1952_);
v___x_1955_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1954_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1965_; 
lean_dec_ref(v_a_1950_);
lean_dec(v___y_1949_);
lean_dec(v_a_1921_);
lean_dec(v_a_1911_);
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1958_ = v___x_1955_;
v_isShared_1959_ = v_isSharedCheck_1965_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1955_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1965_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1963_; 
v___x_1960_ = ((lean_object*)(l_Lake_Manifest_fromJson_x3f___closed__0));
v___x_1961_ = lean_string_append(v___x_1960_, v_a_1956_);
lean_dec(v_a_1956_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1961_);
v___x_1963_ = v___x_1958_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
else
{
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_dec_ref(v_a_1950_);
lean_dec(v___y_1949_);
lean_dec(v_a_1921_);
lean_dec(v_a_1911_);
v_a_1966_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1955_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1955_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
lean_ctor_set_tag(v___x_1968_, 0);
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
else
{
lean_object* v_a_1974_; 
v_a_1974_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_a_1974_);
lean_dec_ref(v___x_1955_);
v___y_1923_ = v___y_1948_;
v___y_1924_ = v___y_1949_;
v___y_1925_ = v_a_1950_;
v_a_1926_ = v_a_1974_;
goto v___jp_1922_;
}
}
}
}
v___jp_1975_:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lake_defaultLakeDir;
v___y_1948_ = v___y_1976_;
v___y_1949_ = v___y_1977_;
v_a_1950_ = v___x_1978_;
goto v___jp_1947_;
}
v___jp_1979_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__5));
v___x_1983_ = l_Lake_JsonObject_getJson_x3f(v_a_1911_, v___x_1982_);
if (lean_obj_tag(v___x_1983_) == 0)
{
v___y_1976_ = v___y_1980_;
v___y_1977_ = v_a_1981_;
goto v___jp_1975_;
}
else
{
lean_object* v_val_1984_; lean_object* v___x_1985_; 
v_val_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_val_1984_);
lean_dec_ref(v___x_1983_);
v___x_1985_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1984_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1995_; 
lean_dec(v_a_1981_);
lean_dec(v_a_1921_);
lean_dec(v_a_1911_);
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1988_ = v___x_1985_;
v_isShared_1989_ = v_isSharedCheck_1995_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1995_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1990_ = ((lean_object*)(l_Lake_Manifest_fromJson_x3f___closed__1));
v___x_1991_ = lean_string_append(v___x_1990_, v_a_1986_);
lean_dec(v_a_1986_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v___x_1991_);
v___x_1993_ = v___x_1988_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
else
{
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec(v_a_1981_);
lean_dec(v_a_1921_);
lean_dec(v_a_1911_);
v_a_1996_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1985_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1985_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
lean_ctor_set_tag(v___x_1998_, 0);
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
else
{
lean_object* v_a_2004_; 
v_a_2004_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_a_2004_);
lean_dec_ref(v___x_1985_);
if (lean_obj_tag(v_a_2004_) == 0)
{
v___y_1976_ = v___y_1980_;
v___y_1977_ = v_a_1981_;
goto v___jp_1975_;
}
else
{
lean_object* v_val_2005_; 
v_val_2005_ = lean_ctor_get(v_a_2004_, 0);
lean_inc(v_val_2005_);
lean_dec_ref(v_a_2004_);
v___y_1948_ = v___y_1980_;
v___y_1949_ = v_a_1981_;
v_a_1950_ = v_val_2005_;
goto v___jp_1947_;
}
}
}
}
}
v___jp_2006_:
{
lean_object* v___x_2008_; 
v___x_2008_ = lean_box(0);
v___y_1980_ = v___y_2007_;
v_a_1981_ = v___x_2008_;
goto v___jp_1979_;
}
v___jp_2009_:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_2012_ = l_Lake_JsonObject_getJson_x3f(v_a_1911_, v___x_2011_);
if (lean_obj_tag(v___x_2012_) == 0)
{
v___y_2007_ = v_a_2010_;
goto v___jp_2006_;
}
else
{
lean_object* v_val_2013_; lean_object* v___x_2014_; 
v_val_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_val_2013_);
lean_dec_ref(v___x_2012_);
v___x_2014_ = l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0(v_val_2013_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2024_; 
lean_dec(v_a_1921_);
lean_dec(v_a_1911_);
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2024_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2024_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2019_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__1));
v___x_2020_ = lean_string_append(v___x_2019_, v_a_2015_);
lean_dec(v_a_2015_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2020_);
v___x_2022_ = v___x_2017_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
else
{
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec(v_a_1921_);
lean_dec(v_a_1911_);
v_a_2025_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_2014_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2014_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
lean_ctor_set_tag(v___x_2027_, 0);
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
else
{
lean_object* v_a_2033_; 
v_a_2033_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2033_);
lean_dec_ref(v___x_2014_);
if (lean_obj_tag(v_a_2033_) == 0)
{
v___y_2007_ = v_a_2010_;
goto v___jp_2006_;
}
else
{
lean_object* v_val_2034_; 
v_val_2034_ = lean_ctor_get(v_a_2033_, 0);
lean_inc(v_val_2034_);
lean_dec_ref(v_a_2033_);
v___y_1980_ = v_a_2010_;
v_a_1981_ = v_val_2034_;
goto v___jp_1979_;
}
}
}
}
}
v___jp_2035_:
{
uint8_t v___x_2036_; 
v___x_2036_ = 0;
v_a_2010_ = v___x_2036_;
goto v___jp_2009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_parse(lean_object* v_data_2065_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_Lean_Json_parse(v_data_2065_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2076_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2076_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2076_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2074_; 
v___x_2071_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2072_ = lean_string_append(v___x_2071_, v_a_2067_);
lean_dec(v_a_2067_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2072_);
v___x_2074_ = v___x_2069_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2078_; 
v_a_2077_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2077_);
lean_dec_ref(v___x_2066_);
v___x_2078_ = l_Lake_Manifest_fromJson_x3f(v_a_2077_);
return v___x_2078_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load(lean_object* v_file_2080_){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = l_IO_FS_readFile(v_file_2080_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2111_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2085_ = v___x_2082_;
v_isShared_2086_ = v_isSharedCheck_2111_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2082_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2111_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v_a_2088_; lean_object* v___x_2096_; 
v___x_2096_ = l_Lean_Json_parse(v_a_2083_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref(v___x_2096_);
v___x_2098_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2099_ = lean_string_append(v___x_2098_, v_a_2097_);
lean_dec(v_a_2097_);
v_a_2088_ = v___x_2099_;
goto v___jp_2087_;
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2101_; 
v_a_2100_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2100_);
lean_dec_ref(v___x_2096_);
v___x_2101_ = l_Lake_Manifest_fromJson_x3f(v_a_2100_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref(v___x_2101_);
v_a_2088_ = v_a_2102_;
goto v___jp_2087_;
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_del_object(v___x_2085_);
lean_dec_ref(v_file_2080_);
v_a_2103_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2101_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2101_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
lean_ctor_set_tag(v___x_2105_, 0);
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
v___jp_2087_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2094_; 
v___x_2089_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2090_ = lean_string_append(v_file_2080_, v___x_2089_);
v___x_2091_ = lean_string_append(v___x_2090_, v_a_2088_);
lean_dec_ref(v_a_2088_);
v___x_2092_ = lean_mk_io_user_error(v___x_2091_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set_tag(v___x_2085_, 1);
lean_ctor_set(v___x_2085_, 0, v___x_2092_);
v___x_2094_ = v___x_2085_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec_ref(v_file_2080_);
v_a_2112_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2082_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2082_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load___boxed(lean_object* v_file_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lake_Manifest_load(v_file_2120_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f(lean_object* v_file_2123_){
_start:
{
lean_object* v_a_2126_; lean_object* v___x_2130_; 
v___x_2130_ = l_IO_FS_readFile(v_file_2123_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2159_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2133_ = v___x_2130_;
v_isShared_2134_ = v_isSharedCheck_2159_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2130_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2159_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v_a_2136_; lean_object* v___x_2141_; 
v___x_2141_ = l_Lean_Json_parse(v_a_2131_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
lean_del_object(v___x_2133_);
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref(v___x_2141_);
v___x_2143_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2144_ = lean_string_append(v___x_2143_, v_a_2142_);
lean_dec(v_a_2142_);
v_a_2136_ = v___x_2144_;
goto v___jp_2135_;
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2146_; 
v_a_2145_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2145_);
lean_dec_ref(v___x_2141_);
v___x_2146_ = l_Lake_Manifest_fromJson_x3f(v_a_2145_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; 
lean_del_object(v___x_2133_);
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref(v___x_2146_);
v_a_2136_ = v_a_2147_;
goto v___jp_2135_;
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2158_; 
lean_dec_ref(v_file_2123_);
v_a_2148_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2150_ = v___x_2146_;
v_isShared_2151_ = v_isSharedCheck_2158_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2146_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2158_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v___x_2155_; 
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 0, v___x_2153_);
v___x_2155_ = v___x_2133_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2153_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
}
v___jp_2135_:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2137_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2138_ = lean_string_append(v_file_2123_, v___x_2137_);
v___x_2139_ = lean_string_append(v___x_2138_, v_a_2136_);
lean_dec_ref(v_a_2136_);
v___x_2140_ = lean_mk_io_user_error(v___x_2139_);
v_a_2126_ = v___x_2140_;
goto v___jp_2125_;
}
}
}
else
{
lean_object* v_a_2160_; 
lean_dec_ref(v_file_2123_);
v_a_2160_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2160_);
lean_dec_ref(v___x_2130_);
v_a_2126_ = v_a_2160_;
goto v___jp_2125_;
}
v___jp_2125_:
{
if (lean_obj_tag(v_a_2126_) == 11)
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
lean_dec_ref(v_a_2126_);
v___x_2127_ = lean_box(0);
v___x_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
return v___x_2128_;
}
else
{
lean_object* v___x_2129_; 
v___x_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2129_, 0, v_a_2126_);
return v___x_2129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f___boxed(lean_object* v_file_2161_, lean_object* v_a_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Lake_Manifest_load_x3f(v_file_2161_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_save(lean_object* v_self_2164_, lean_object* v_manifestFile_2165_){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v_contents_2169_; uint32_t v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2167_ = l_Lake_Manifest_toJson(v_self_2164_);
v___x_2168_ = lean_unsigned_to_nat(80u);
v_contents_2169_ = l_Lean_Json_pretty(v___x_2167_, v___x_2168_);
v___x_2170_ = 10;
v___x_2171_ = lean_string_push(v_contents_2169_, v___x_2170_);
v___x_2172_ = l_IO_FS_writeFile(v_manifestFile_2165_, v___x_2171_);
lean_dec_ref(v___x_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_save___boxed(lean_object* v_self_2173_, lean_object* v_manifestFile_2174_, lean_object* v_a_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Lake_Manifest_save(v_self_2173_, v_manifestFile_2174_);
lean_dec_ref(v_manifestFile_2174_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_decodeEntries(lean_object* v_data_2177_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_Lean_Json_getObj_x3f(v_data_2177_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2178_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2178_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2188_; 
v_a_2187_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2187_);
lean_dec_ref(v___x_2178_);
v___x_2188_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_a_2187_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec(v_a_2187_);
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2188_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2188_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v_a_2197_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2197_);
lean_dec_ref(v___x_2188_);
v___x_2198_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2199_, 0, v_a_2197_);
lean_ctor_set(v___x_2199_, 1, v___x_2198_);
v___x_2200_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(v___x_2199_, v_a_2187_);
lean_dec(v_a_2187_);
lean_dec_ref(v___x_2199_);
return v___x_2200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_parseEntries(lean_object* v_data_2201_){
_start:
{
lean_object* v___x_2202_; 
v___x_2202_ = l_Lean_Json_parse(v_data_2201_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2212_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2205_ = v___x_2202_;
v_isShared_2206_ = v_isSharedCheck_2212_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2212_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2207_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2208_ = lean_string_append(v___x_2207_, v_a_2203_);
lean_dec(v_a_2203_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2208_);
v___x_2210_ = v___x_2205_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2214_; 
v_a_2213_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2213_);
lean_dec_ref(v___x_2202_);
v___x_2214_ = l_Lake_Manifest_decodeEntries(v_a_2213_);
return v___x_2214_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_loadEntries(lean_object* v_file_2215_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_IO_FS_readFile(v_file_2215_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2246_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2220_ = v___x_2217_;
v_isShared_2221_ = v_isSharedCheck_2246_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2217_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2246_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v_a_2223_; lean_object* v___x_2231_; 
v___x_2231_ = l_Lean_Json_parse(v_a_2218_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2232_);
lean_dec_ref(v___x_2231_);
v___x_2233_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2234_ = lean_string_append(v___x_2233_, v_a_2232_);
lean_dec(v_a_2232_);
v_a_2223_ = v___x_2234_;
goto v___jp_2222_;
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2236_; 
v_a_2235_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2235_);
lean_dec_ref(v___x_2231_);
v___x_2236_ = l_Lake_Manifest_decodeEntries(v_a_2235_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2237_);
lean_dec_ref(v___x_2236_);
v_a_2223_ = v_a_2237_;
goto v___jp_2222_;
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_del_object(v___x_2220_);
lean_dec_ref(v_file_2215_);
v_a_2238_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2236_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2236_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
lean_ctor_set_tag(v___x_2240_, 0);
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
v___jp_2222_:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2229_; 
v___x_2224_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2225_ = lean_string_append(v_file_2215_, v___x_2224_);
v___x_2226_ = lean_string_append(v___x_2225_, v_a_2223_);
lean_dec_ref(v_a_2223_);
v___x_2227_ = lean_mk_io_user_error(v___x_2226_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set_tag(v___x_2220_, 1);
lean_ctor_set(v___x_2220_, 0, v___x_2227_);
v___x_2229_ = v___x_2220_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2227_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec_ref(v_file_2215_);
v_a_2247_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2217_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2217_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_loadEntries___boxed(lean_object* v_file_2255_, lean_object* v_a_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lake_Manifest_loadEntries(v_file_2255_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries(lean_object* v_file_2258_){
_start:
{
lean_object* v_a_2261_; lean_object* v___x_2270_; 
v___x_2270_ = l_IO_FS_readFile(v_file_2258_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2292_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2273_ = v___x_2270_;
v_isShared_2274_ = v_isSharedCheck_2292_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2270_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2292_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v_a_2276_; lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_Json_parse(v_a_2271_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
lean_del_object(v___x_2273_);
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref(v___x_2281_);
v___x_2283_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2284_ = lean_string_append(v___x_2283_, v_a_2282_);
lean_dec(v_a_2282_);
v_a_2276_ = v___x_2284_;
goto v___jp_2275_;
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2286_; 
v_a_2285_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2285_);
lean_dec_ref(v___x_2281_);
v___x_2286_ = l_Lake_Manifest_decodeEntries(v_a_2285_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; 
lean_del_object(v___x_2273_);
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref(v___x_2286_);
v_a_2276_ = v_a_2287_;
goto v___jp_2275_;
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; 
lean_dec_ref(v_file_2258_);
v_a_2288_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2288_);
lean_dec_ref(v___x_2286_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 0, v_a_2288_);
v___x_2290_ = v___x_2273_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
v___jp_2275_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2277_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
lean_inc_ref(v_file_2258_);
v___x_2278_ = lean_string_append(v_file_2258_, v___x_2277_);
v___x_2279_ = lean_string_append(v___x_2278_, v_a_2276_);
lean_dec_ref(v_a_2276_);
v___x_2280_ = lean_mk_io_user_error(v___x_2279_);
v_a_2261_ = v___x_2280_;
goto v___jp_2260_;
}
}
}
else
{
lean_object* v_a_2293_; 
v_a_2293_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2293_);
lean_dec_ref(v___x_2270_);
v_a_2261_ = v_a_2293_;
goto v___jp_2260_;
}
v___jp_2260_:
{
if (lean_obj_tag(v_a_2261_) == 11)
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
lean_dec_ref(v_a_2261_);
lean_dec_ref(v_file_2258_);
v___x_2262_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__1));
v___x_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
return v___x_2263_;
}
else
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2264_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2265_ = lean_string_append(v_file_2258_, v___x_2264_);
v___x_2266_ = lean_io_error_to_string(v_a_2261_);
v___x_2267_ = lean_string_append(v___x_2265_, v___x_2266_);
lean_dec_ref(v___x_2266_);
v___x_2268_ = lean_mk_io_user_error(v___x_2267_);
v___x_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
return v___x_2269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries___boxed(lean_object* v_file_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lake_Manifest_tryLoadEntries(v_file_2294_);
return v_res_2296_;
}
}
static lean_object* _init_l_Lake_Manifest_saveEntries___closed__0(void){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2297_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__2, &l_Lake_Manifest_toJson___closed__2_once, _init_l_Lake_Manifest_toJson___closed__2);
v___x_2298_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8));
v___x_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
lean_ctor_set(v___x_2299_, 1, v___x_2297_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries(lean_object* v_file_2300_, lean_object* v_entries_2301_){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v_contents_2312_; uint32_t v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2303_ = lean_obj_once(&l_Lake_Manifest_saveEntries___closed__0, &l_Lake_Manifest_saveEntries___closed__0_once, _init_l_Lake_Manifest_saveEntries___closed__0);
v___x_2304_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__7));
v___x_2305_ = l_Array_toJson___at___00Lake_Manifest_toJson_spec__0(v_entries_2301_);
v___x_2306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2304_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
v___x_2307_ = lean_box(0);
v___x_2308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2306_);
lean_ctor_set(v___x_2308_, 1, v___x_2307_);
v___x_2309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2303_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
v___x_2310_ = l_Lean_Json_mkObj(v___x_2309_);
v___x_2311_ = lean_unsigned_to_nat(80u);
v_contents_2312_ = l_Lean_Json_pretty(v___x_2310_, v___x_2311_);
v___x_2313_ = 10;
v___x_2314_ = lean_string_push(v_contents_2312_, v___x_2313_);
v___x_2315_ = l_IO_FS_writeFile(v_file_2300_, v___x_2314_);
lean_dec_ref(v___x_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries___boxed(lean_object* v_file_2316_, lean_object* v_entries_2317_, lean_object* v_a_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lake_Manifest_saveEntries(v_file_2316_, v_entries_2317_);
lean_dec_ref(v_file_2316_);
return v_res_2319_;
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
l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6_default = _init_l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6_default();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6_default);
l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6 = _init_l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6();
lean_mark_persistent(l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6);
l_Lake_instInhabitedPackageEntrySrc_default = _init_l_Lake_instInhabitedPackageEntrySrc_default();
lean_mark_persistent(l_Lake_instInhabitedPackageEntrySrc_default);
l_Lake_instInhabitedPackageEntrySrc = _init_l_Lake_instInhabitedPackageEntrySrc();
lean_mark_persistent(l_Lake_instInhabitedPackageEntrySrc);
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
