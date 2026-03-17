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
static const lean_ctor_object l_Lake_Manifest_version___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_string_object l_Lake_Manifest_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "lakeDir"};
static const lean_object* l_Lake_Manifest_toJson___closed__4 = (const lean_object*)&l_Lake_Manifest_toJson___closed__4_value;
static const lean_string_object l_Lake_Manifest_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "packagesDir"};
static const lean_object* l_Lake_Manifest_toJson___closed__5 = (const lean_object*)&l_Lake_Manifest_toJson___closed__5_value;
static const lean_string_object l_Lake_Manifest_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "packages"};
static const lean_object* l_Lake_Manifest_toJson___closed__6 = (const lean_object*)&l_Lake_Manifest_toJson___closed__6_value;
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
static const lean_string_object l_Lake_Manifest_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "packagesDir: "};
static const lean_object* l_Lake_Manifest_fromJson_x3f___closed__0 = (const lean_object*)&l_Lake_Manifest_fromJson_x3f___closed__0_value;
static const lean_string_object l_Lake_Manifest_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "lakeDir: "};
static const lean_object* l_Lake_Manifest_fromJson_x3f___closed__1 = (const lean_object*)&l_Lake_Manifest_fromJson_x3f___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorIdx(lean_object* v_x_9_){
_start:
{
if (lean_obj_tag(v_x_9_) == 0)
{
lean_object* v___x_10_; 
v___x_10_ = lean_unsigned_to_nat(0u);
return v___x_10_;
}
else
{
lean_object* v___x_11_; 
v___x_11_ = lean_unsigned_to_nat(1u);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorIdx___boxed(lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorIdx(v_x_12_);
lean_dec_ref(v_x_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(lean_object* v_t_14_, lean_object* v_k_15_){
_start:
{
if (lean_obj_tag(v_t_14_) == 0)
{
lean_object* v_name_16_; lean_object* v_opts_17_; uint8_t v_inherited_18_; lean_object* v_dir_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v_name_16_ = lean_ctor_get(v_t_14_, 0);
lean_inc(v_name_16_);
v_opts_17_ = lean_ctor_get(v_t_14_, 1);
lean_inc(v_opts_17_);
v_inherited_18_ = lean_ctor_get_uint8(v_t_14_, sizeof(void*)*3);
v_dir_19_ = lean_ctor_get(v_t_14_, 2);
lean_inc_ref(v_dir_19_);
lean_dec_ref(v_t_14_);
v___x_20_ = lean_box(v_inherited_18_);
v___x_21_ = lean_apply_4(v_k_15_, v_name_16_, v_opts_17_, v___x_20_, v_dir_19_);
return v___x_21_;
}
else
{
lean_object* v_name_22_; lean_object* v_opts_23_; uint8_t v_inherited_24_; lean_object* v_url_25_; lean_object* v_rev_26_; lean_object* v_inputRev_x3f_27_; lean_object* v_subDir_x3f_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v_name_22_ = lean_ctor_get(v_t_14_, 0);
lean_inc(v_name_22_);
v_opts_23_ = lean_ctor_get(v_t_14_, 1);
lean_inc(v_opts_23_);
v_inherited_24_ = lean_ctor_get_uint8(v_t_14_, sizeof(void*)*6);
v_url_25_ = lean_ctor_get(v_t_14_, 2);
lean_inc_ref(v_url_25_);
v_rev_26_ = lean_ctor_get(v_t_14_, 3);
lean_inc_ref(v_rev_26_);
v_inputRev_x3f_27_ = lean_ctor_get(v_t_14_, 4);
lean_inc(v_inputRev_x3f_27_);
v_subDir_x3f_28_ = lean_ctor_get(v_t_14_, 5);
lean_inc(v_subDir_x3f_28_);
lean_dec_ref(v_t_14_);
v___x_29_ = lean_box(v_inherited_24_);
v___x_30_ = lean_apply_7(v_k_15_, v_name_22_, v_opts_23_, v___x_29_, v_url_25_, v_rev_26_, v_inputRev_x3f_27_, v_subDir_x3f_28_);
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim(lean_object* v_motive_31_, lean_object* v_ctorIdx_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_k_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(v_t_33_, v_k_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___boxed(lean_object* v_motive_37_, lean_object* v_ctorIdx_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_k_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim(v_motive_37_, v_ctorIdx_38_, v_t_39_, v_h_40_, v_k_41_);
lean_dec(v_ctorIdx_38_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_path_elim___redArg(lean_object* v_t_43_, lean_object* v_path_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(v_t_43_, v_path_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_path_elim(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_path_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(v_t_47_, v_path_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_git_elim___redArg(lean_object* v_t_51_, lean_object* v_git_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(v_t_51_, v_git_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_git_elim(lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_git_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(v_t_55_, v_git_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(lean_object* v_x_61_){
_start:
{
if (lean_obj_tag(v_x_61_) == 0)
{
lean_object* v___x_62_; 
v___x_62_ = ((lean_object*)(l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0));
return v___x_62_;
}
else
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Json_getStr_x3f(v_x_61_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v_a_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_71_; 
v_a_64_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_71_ == 0)
{
v___x_66_ = v___x_63_;
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_a_64_);
lean_dec(v___x_63_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_69_; 
if (v_isShared_67_ == 0)
{
v___x_69_ = v___x_66_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_a_64_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
else
{
lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_80_; 
v_a_72_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_80_ == 0)
{
v___x_74_ = v___x_63_;
v_isShared_75_ = v_isSharedCheck_80_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_dec(v___x_63_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_80_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_76_; lean_object* v___x_78_; 
v___x_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_76_, 0, v_a_72_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 0, v___x_76_);
v___x_78_ = v___x_74_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(lean_object* v_x_81_){
_start:
{
if (lean_obj_tag(v_x_81_) == 0)
{
lean_object* v___x_82_; 
v___x_82_ = ((lean_object*)(l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0));
return v___x_82_;
}
else
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_Json_getStr_x3f(v_x_81_);
if (lean_obj_tag(v___x_83_) == 0)
{
lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_91_; 
v_a_84_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_91_ == 0)
{
v___x_86_ = v___x_83_;
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v___x_83_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_89_; 
if (v_isShared_87_ == 0)
{
v___x_89_ = v___x_86_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_a_84_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
else
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_100_; 
v_a_92_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_100_ == 0)
{
v___x_94_ = v___x_83_;
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_83_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_96_, 0, v_a_92_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_96_);
v___x_98_ = v___x_94_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0(lean_object* v_init_104_, lean_object* v_x_105_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
lean_object* v_k_106_; lean_object* v_v_107_; lean_object* v_l_108_; lean_object* v_r_109_; lean_object* v___x_110_; 
v_k_106_ = lean_ctor_get(v_x_105_, 1);
lean_inc(v_k_106_);
v_v_107_ = lean_ctor_get(v_x_105_, 2);
lean_inc(v_v_107_);
v_l_108_ = lean_ctor_get(v_x_105_, 3);
lean_inc(v_l_108_);
v_r_109_ = lean_ctor_get(v_x_105_, 4);
lean_inc(v_r_109_);
lean_dec_ref(v_x_105_);
v___x_110_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0(v_init_104_, v_l_108_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_dec(v_r_109_);
lean_dec(v_v_107_);
lean_dec(v_k_106_);
return v___x_110_;
}
else
{
lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_151_; 
v_a_111_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_151_ == 0)
{
v___x_113_ = v___x_110_;
v_isShared_114_ = v_isSharedCheck_151_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v___x_110_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_151_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_115_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__0));
v___x_116_ = lean_string_dec_eq(v_k_106_, v___x_115_);
if (v___x_116_ == 0)
{
lean_object* v_n_117_; uint8_t v___x_118_; 
lean_inc(v_k_106_);
v_n_117_ = l_String_toName(v_k_106_);
v___x_118_ = l_Lean_Name_isAnonymous(v_n_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; 
lean_del_object(v___x_113_);
lean_dec(v_k_106_);
v___x_119_ = l_Lean_Json_getStr_x3f(v_v_107_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
lean_dec(v_n_117_);
lean_dec(v_a_111_);
lean_dec(v_r_109_);
v_a_120_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_119_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_119_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
else
{
lean_object* v_a_128_; lean_object* v___x_129_; 
v_a_128_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_a_128_);
lean_dec_ref(v___x_119_);
v___x_129_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_117_, v_a_128_, v_a_111_);
v_init_104_ = v___x_129_;
v_x_105_ = v_r_109_;
goto _start;
}
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
lean_dec(v_n_117_);
lean_dec(v_a_111_);
lean_dec(v_r_109_);
lean_dec(v_v_107_);
v___x_131_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__1));
v___x_132_ = lean_string_append(v___x_131_, v_k_106_);
lean_dec(v_k_106_);
v___x_133_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_134_ = lean_string_append(v___x_132_, v___x_133_);
if (v_isShared_114_ == 0)
{
lean_ctor_set_tag(v___x_113_, 0);
lean_ctor_set(v___x_113_, 0, v___x_134_);
v___x_136_ = v___x_113_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
else
{
lean_object* v___x_138_; 
lean_del_object(v___x_113_);
lean_dec(v_k_106_);
v___x_138_ = l_Lean_Json_getStr_x3f(v_v_107_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
lean_dec(v_a_111_);
lean_dec(v_r_109_);
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
lean_object* v_a_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v_a_147_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_147_);
lean_dec_ref(v___x_138_);
v___x_148_ = lean_box(0);
v___x_149_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_148_, v_a_147_, v_a_111_);
v_init_104_ = v___x_149_;
v_x_105_ = v_r_109_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_152_; 
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v_init_104_);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0(lean_object* v_x_154_){
_start:
{
if (lean_obj_tag(v_x_154_) == 5)
{
lean_object* v_kvPairs_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_kvPairs_155_ = lean_ctor_get(v_x_154_, 0);
lean_inc(v_kvPairs_155_);
lean_dec_ref(v_x_154_);
v___x_156_ = lean_box(1);
v___x_157_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0(v___x_156_, v_kvPairs_155_);
return v___x_157_;
}
else
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_158_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0___closed__0));
v___x_159_ = lean_unsigned_to_nat(80u);
v___x_160_ = l_Lean_Json_pretty(v_x_154_, v___x_159_);
v___x_161_ = lean_string_append(v___x_158_, v___x_160_);
lean_dec_ref(v___x_160_);
v___x_162_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_163_ = lean_string_append(v___x_161_, v___x_162_);
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson(lean_object* v_json_227_){
_start:
{
lean_object* v___x_228_; 
lean_inc(v_json_227_);
v___x_228_ = l_Lean_Json_getTag_x3f(v_json_227_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v___x_229_; 
lean_dec(v_json_227_);
v___x_229_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__1));
return v___x_229_;
}
else
{
lean_object* v_val_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v_val_230_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_val_230_);
lean_dec_ref(v___x_228_);
v___x_231_ = lean_box(0);
v___x_232_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2));
v___x_233_ = lean_string_dec_eq(v_val_230_, v___x_232_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_234_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3));
v___x_235_ = lean_string_dec_eq(v_val_230_, v___x_234_);
lean_dec(v_val_230_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; 
lean_dec(v_json_227_);
v___x_236_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__5));
return v___x_236_;
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = lean_unsigned_to_nat(7u);
v___x_238_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__21));
v___x_239_ = l_Lean_Json_parseCtorFields(v_json_227_, v___x_234_, v___x_237_, v___x_238_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
v_a_240_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_239_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_239_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
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
lean_object* v_a_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_a_248_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_a_248_);
lean_dec_ref(v___x_239_);
v___x_249_ = lean_unsigned_to_nat(0u);
v___x_250_ = lean_array_get_borrowed(v___x_231_, v_a_248_, v___x_249_);
lean_inc(v___x_250_);
v___x_251_ = l_Lean_Name_fromJson_x3f(v___x_250_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
lean_dec(v_a_248_);
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
else
{
lean_object* v_a_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_a_260_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_a_260_);
lean_dec_ref(v___x_251_);
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_262_ = lean_array_get_borrowed(v___x_231_, v_a_248_, v___x_261_);
lean_inc(v___x_262_);
v___x_263_ = l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0(v___x_262_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
lean_dec(v_a_260_);
lean_dec(v_a_248_);
v_a_264_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_263_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_263_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
else
{
lean_object* v_a_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v_a_272_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_a_272_);
lean_dec_ref(v___x_263_);
v___x_273_ = lean_unsigned_to_nat(2u);
v___x_274_ = lean_array_get_borrowed(v___x_231_, v_a_248_, v___x_273_);
v___x_275_ = l_Lean_Json_getBool_x3f(v___x_274_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_dec(v_a_272_);
lean_dec(v_a_260_);
lean_dec(v_a_248_);
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
else
{
lean_object* v_a_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v_a_284_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_284_);
lean_dec_ref(v___x_275_);
v___x_285_ = lean_unsigned_to_nat(3u);
v___x_286_ = lean_array_get_borrowed(v___x_231_, v_a_248_, v___x_285_);
lean_inc(v___x_286_);
v___x_287_ = l_Lean_Json_getStr_x3f(v___x_286_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
lean_dec(v_a_284_);
lean_dec(v_a_272_);
lean_dec(v_a_260_);
lean_dec(v_a_248_);
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
else
{
lean_object* v_a_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_a_296_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_a_296_);
lean_dec_ref(v___x_287_);
v___x_297_ = lean_unsigned_to_nat(4u);
v___x_298_ = lean_array_get_borrowed(v___x_231_, v_a_248_, v___x_297_);
lean_inc(v___x_298_);
v___x_299_ = l_Lean_Json_getStr_x3f(v___x_298_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec(v_a_296_);
lean_dec(v_a_284_);
lean_dec(v_a_272_);
lean_dec(v_a_260_);
lean_dec(v_a_248_);
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
lean_object* v_a_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_a_308_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_308_);
lean_dec_ref(v___x_299_);
v___x_309_ = lean_unsigned_to_nat(5u);
v___x_310_ = lean_array_get_borrowed(v___x_231_, v_a_248_, v___x_309_);
lean_inc(v___x_310_);
v___x_311_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(v___x_310_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
lean_dec(v_a_308_);
lean_dec(v_a_296_);
lean_dec(v_a_284_);
lean_dec(v_a_272_);
lean_dec(v_a_260_);
lean_dec(v_a_248_);
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
else
{
lean_object* v_a_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_a_320_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_320_);
lean_dec_ref(v___x_311_);
v___x_321_ = lean_unsigned_to_nat(6u);
v___x_322_ = lean_array_get(v___x_231_, v_a_248_, v___x_321_);
lean_dec(v_a_248_);
v___x_323_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v___x_322_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec(v_a_320_);
lean_dec(v_a_308_);
lean_dec(v_a_296_);
lean_dec(v_a_284_);
lean_dec(v_a_272_);
lean_dec(v_a_260_);
v_a_324_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_323_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_323_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_341_; 
v_a_332_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_341_ == 0)
{
v___x_334_ = v___x_323_;
v_isShared_335_ = v_isSharedCheck_341_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_323_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_341_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v___x_339_; 
v___x_336_ = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(v___x_336_, 0, v_a_260_);
lean_ctor_set(v___x_336_, 1, v_a_272_);
lean_ctor_set(v___x_336_, 2, v_a_296_);
lean_ctor_set(v___x_336_, 3, v_a_308_);
lean_ctor_set(v___x_336_, 4, v_a_320_);
lean_ctor_set(v___x_336_, 5, v_a_332_);
v___x_337_ = lean_unbox(v_a_284_);
lean_dec(v_a_284_);
lean_ctor_set_uint8(v___x_336_, sizeof(void*)*6, v___x_337_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_336_);
v___x_339_ = v___x_334_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_336_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
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
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
lean_dec(v_val_230_);
v___x_342_ = lean_unsigned_to_nat(4u);
v___x_343_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__25));
v___x_344_ = l_Lean_Json_parseCtorFields(v_json_227_, v___x_232_, v___x_342_, v___x_343_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_344_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
else
{
lean_object* v_a_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v_a_353_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_353_);
lean_dec_ref(v___x_344_);
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = lean_array_get_borrowed(v___x_231_, v_a_353_, v___x_354_);
lean_inc(v___x_355_);
v___x_356_ = l_Lean_Name_fromJson_x3f(v___x_355_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_dec(v_a_353_);
v_a_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
else
{
lean_object* v_a_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_a_365_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_365_);
lean_dec_ref(v___x_356_);
v___x_366_ = lean_unsigned_to_nat(1u);
v___x_367_ = lean_array_get_borrowed(v___x_231_, v_a_353_, v___x_366_);
lean_inc(v___x_367_);
v___x_368_ = l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0(v___x_367_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_dec(v_a_365_);
lean_dec(v_a_353_);
v_a_369_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_368_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
else
{
lean_object* v_a_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_a_377_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_377_);
lean_dec_ref(v___x_368_);
v___x_378_ = lean_unsigned_to_nat(2u);
v___x_379_ = lean_array_get_borrowed(v___x_231_, v_a_353_, v___x_378_);
v___x_380_ = l_Lean_Json_getBool_x3f(v___x_379_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec(v_a_377_);
lean_dec(v_a_365_);
lean_dec(v_a_353_);
v_a_381_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_380_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v_a_389_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_389_);
lean_dec_ref(v___x_380_);
v___x_390_ = lean_unsigned_to_nat(3u);
v___x_391_ = lean_array_get(v___x_231_, v_a_353_, v___x_390_);
lean_dec(v_a_353_);
v___x_392_ = l_Lean_Json_getStr_x3f(v___x_391_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec(v_a_389_);
lean_dec(v_a_377_);
lean_dec(v_a_365_);
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_410_; 
v_a_401_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_410_ == 0)
{
v___x_403_ = v___x_392_;
v_isShared_404_ = v_isSharedCheck_410_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_392_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_410_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; uint8_t v___x_406_; lean_object* v___x_408_; 
v___x_405_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_405_, 0, v_a_365_);
lean_ctor_set(v___x_405_, 1, v_a_377_);
lean_ctor_set(v___x_405_, 2, v_a_401_);
v___x_406_ = lean_unbox(v_a_389_);
lean_dec(v_a_389_);
lean_ctor_set_uint8(v___x_405_, sizeof(void*)*3, v___x_406_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_405_);
v___x_408_ = v___x_403_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_405_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
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
LEAN_EXPORT lean_object* l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__1(lean_object* v_x_413_){
_start:
{
if (lean_obj_tag(v_x_413_) == 0)
{
lean_object* v___x_414_; 
v___x_414_ = lean_box(0);
return v___x_414_;
}
else
{
lean_object* v_val_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
v_val_415_ = lean_ctor_get(v_x_413_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v_x_413_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v_x_413_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_val_415_);
lean_dec(v_x_413_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set_tag(v___x_417_, 3);
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_val_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(lean_object* v_x_423_){
_start:
{
if (lean_obj_tag(v_x_423_) == 0)
{
lean_object* v___x_424_; 
v___x_424_ = lean_box(0);
return v___x_424_;
}
else
{
lean_object* v_val_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_433_; 
v_val_425_ = lean_ctor_get(v_x_423_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v_x_423_);
if (v_isSharedCheck_433_ == 0)
{
v___x_427_ = v_x_423_;
v_isShared_428_ = v_isSharedCheck_433_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_val_425_);
lean_dec(v_x_423_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_433_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_429_ = l_Lake_mkRelPathString(v_val_425_);
if (v_isShared_428_ == 0)
{
lean_ctor_set_tag(v___x_427_, 3);
lean_ctor_set(v___x_427_, 0, v___x_429_);
v___x_431_ = v___x_427_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(lean_object* v_msg_434_){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_box(1);
v___x_436_ = lean_panic_fn(v___x_435_, v_msg_434_);
return v___x_436_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_440_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__2));
v___x_441_ = lean_unsigned_to_nat(35u);
v___x_442_ = lean_unsigned_to_nat(276u);
v___x_443_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__1));
v___x_444_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__0));
v___x_445_ = l_mkPanicMessageWithDecl(v___x_444_, v___x_443_, v___x_442_, v___x_441_, v___x_440_);
return v___x_445_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_446_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__2));
v___x_447_ = lean_unsigned_to_nat(21u);
v___x_448_ = lean_unsigned_to_nat(277u);
v___x_449_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__1));
v___x_450_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__0));
v___x_451_ = l_mkPanicMessageWithDecl(v___x_450_, v___x_449_, v___x_448_, v___x_447_, v___x_446_);
return v___x_451_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_454_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__6));
v___x_455_ = lean_unsigned_to_nat(35u);
v___x_456_ = lean_unsigned_to_nat(182u);
v___x_457_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__5));
v___x_458_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__0));
v___x_459_ = l_mkPanicMessageWithDecl(v___x_458_, v___x_457_, v___x_456_, v___x_455_, v___x_454_);
return v___x_459_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_460_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__6));
v___x_461_ = lean_unsigned_to_nat(21u);
v___x_462_ = lean_unsigned_to_nat(183u);
v___x_463_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__5));
v___x_464_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__0));
v___x_465_ = l_mkPanicMessageWithDecl(v___x_464_, v___x_463_, v___x_462_, v___x_461_, v___x_460_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(lean_object* v_k_466_, lean_object* v_v_467_, lean_object* v_t_468_){
_start:
{
if (lean_obj_tag(v_t_468_) == 0)
{
lean_object* v_size_469_; lean_object* v_k_470_; lean_object* v_v_471_; lean_object* v_l_472_; lean_object* v_r_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_830_; 
v_size_469_ = lean_ctor_get(v_t_468_, 0);
v_k_470_ = lean_ctor_get(v_t_468_, 1);
v_v_471_ = lean_ctor_get(v_t_468_, 2);
v_l_472_ = lean_ctor_get(v_t_468_, 3);
v_r_473_ = lean_ctor_get(v_t_468_, 4);
v_isSharedCheck_830_ = !lean_is_exclusive(v_t_468_);
if (v_isSharedCheck_830_ == 0)
{
v___x_475_ = v_t_468_;
v_isShared_476_ = v_isSharedCheck_830_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_r_473_);
lean_inc(v_l_472_);
lean_inc(v_v_471_);
lean_inc(v_k_470_);
lean_inc(v_size_469_);
lean_dec(v_t_468_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_830_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
uint8_t v___x_477_; 
v___x_477_ = lean_string_dec_lt(v_k_466_, v_k_470_);
if (v___x_477_ == 0)
{
uint8_t v___x_478_; 
v___x_478_ = lean_string_dec_eq(v_k_466_, v_k_470_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
lean_dec(v_size_469_);
v___x_479_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(v_k_466_, v_v_467_, v_r_473_);
if (lean_obj_tag(v_l_472_) == 0)
{
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_size_480_; lean_object* v_size_481_; lean_object* v_k_482_; lean_object* v_v_483_; lean_object* v_l_484_; lean_object* v_r_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_size_480_ = lean_ctor_get(v_l_472_, 0);
v_size_481_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_size_481_);
v_k_482_ = lean_ctor_get(v___x_479_, 1);
lean_inc(v_k_482_);
v_v_483_ = lean_ctor_get(v___x_479_, 2);
lean_inc(v_v_483_);
v_l_484_ = lean_ctor_get(v___x_479_, 3);
lean_inc(v_l_484_);
v_r_485_ = lean_ctor_get(v___x_479_, 4);
lean_inc(v_r_485_);
v___x_486_ = lean_unsigned_to_nat(3u);
v___x_487_ = lean_nat_mul(v___x_486_, v_size_480_);
v___x_488_ = lean_nat_dec_lt(v___x_487_, v_size_481_);
lean_dec(v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_493_; 
lean_dec(v_r_485_);
lean_dec(v_l_484_);
lean_dec(v_v_483_);
lean_dec(v_k_482_);
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = lean_nat_add(v___x_489_, v_size_480_);
v___x_491_ = lean_nat_add(v___x_490_, v_size_481_);
lean_dec(v_size_481_);
lean_dec(v___x_490_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v___x_479_);
lean_ctor_set(v___x_475_, 0, v___x_491_);
v___x_493_ = v___x_475_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_494_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_494_, 3, v_l_472_);
lean_ctor_set(v_reuseFailAlloc_494_, 4, v___x_479_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
else
{
lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_564_; 
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; lean_object* v_unused_566_; lean_object* v_unused_567_; lean_object* v_unused_568_; lean_object* v_unused_569_; 
v_unused_565_ = lean_ctor_get(v___x_479_, 4);
lean_dec(v_unused_565_);
v_unused_566_ = lean_ctor_get(v___x_479_, 3);
lean_dec(v_unused_566_);
v_unused_567_ = lean_ctor_get(v___x_479_, 2);
lean_dec(v_unused_567_);
v_unused_568_ = lean_ctor_get(v___x_479_, 1);
lean_dec(v_unused_568_);
v_unused_569_ = lean_ctor_get(v___x_479_, 0);
lean_dec(v_unused_569_);
v___x_496_ = v___x_479_;
v_isShared_497_ = v_isSharedCheck_564_;
goto v_resetjp_495_;
}
else
{
lean_dec(v___x_479_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_564_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
if (lean_obj_tag(v_l_484_) == 0)
{
if (lean_obj_tag(v_r_485_) == 0)
{
lean_object* v_size_498_; lean_object* v_k_499_; lean_object* v_v_500_; lean_object* v_l_501_; lean_object* v_r_502_; lean_object* v_size_503_; lean_object* v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v_size_498_ = lean_ctor_get(v_l_484_, 0);
v_k_499_ = lean_ctor_get(v_l_484_, 1);
v_v_500_ = lean_ctor_get(v_l_484_, 2);
v_l_501_ = lean_ctor_get(v_l_484_, 3);
v_r_502_ = lean_ctor_get(v_l_484_, 4);
v_size_503_ = lean_ctor_get(v_r_485_, 0);
v___x_504_ = lean_unsigned_to_nat(2u);
v___x_505_ = lean_nat_mul(v___x_504_, v_size_503_);
v___x_506_ = lean_nat_dec_lt(v_size_498_, v___x_505_);
lean_dec(v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_535_; 
lean_inc(v_r_502_);
lean_inc(v_l_501_);
lean_inc(v_v_500_);
lean_inc(v_k_499_);
v_isSharedCheck_535_ = !lean_is_exclusive(v_l_484_);
if (v_isSharedCheck_535_ == 0)
{
lean_object* v_unused_536_; lean_object* v_unused_537_; lean_object* v_unused_538_; lean_object* v_unused_539_; lean_object* v_unused_540_; 
v_unused_536_ = lean_ctor_get(v_l_484_, 4);
lean_dec(v_unused_536_);
v_unused_537_ = lean_ctor_get(v_l_484_, 3);
lean_dec(v_unused_537_);
v_unused_538_ = lean_ctor_get(v_l_484_, 2);
lean_dec(v_unused_538_);
v_unused_539_ = lean_ctor_get(v_l_484_, 1);
lean_dec(v_unused_539_);
v_unused_540_ = lean_ctor_get(v_l_484_, 0);
lean_dec(v_unused_540_);
v___x_508_ = v_l_484_;
v_isShared_509_ = v_isSharedCheck_535_;
goto v_resetjp_507_;
}
else
{
lean_dec(v_l_484_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_535_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_525_; 
v___x_510_ = lean_unsigned_to_nat(1u);
v___x_511_ = lean_nat_add(v___x_510_, v_size_480_);
v___x_512_ = lean_nat_add(v___x_511_, v_size_481_);
lean_dec(v_size_481_);
if (lean_obj_tag(v_l_501_) == 0)
{
lean_object* v_size_533_; 
v_size_533_ = lean_ctor_get(v_l_501_, 0);
lean_inc(v_size_533_);
v___y_525_ = v_size_533_;
goto v___jp_524_;
}
else
{
lean_object* v___x_534_; 
v___x_534_ = lean_unsigned_to_nat(0u);
v___y_525_ = v___x_534_;
goto v___jp_524_;
}
v___jp_513_:
{
lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_517_ = lean_nat_add(v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec(v___y_515_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 4, v_r_485_);
lean_ctor_set(v___x_508_, 3, v_r_502_);
lean_ctor_set(v___x_508_, 2, v_v_483_);
lean_ctor_set(v___x_508_, 1, v_k_482_);
lean_ctor_set(v___x_508_, 0, v___x_517_);
v___x_519_ = v___x_508_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_k_482_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v_v_483_);
lean_ctor_set(v_reuseFailAlloc_523_, 3, v_r_502_);
lean_ctor_set(v_reuseFailAlloc_523_, 4, v_r_485_);
v___x_519_ = v_reuseFailAlloc_523_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v___x_521_; 
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 4, v___x_519_);
lean_ctor_set(v___x_496_, 3, v___y_514_);
lean_ctor_set(v___x_496_, 2, v_v_500_);
lean_ctor_set(v___x_496_, 1, v_k_499_);
lean_ctor_set(v___x_496_, 0, v___x_512_);
v___x_521_ = v___x_496_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_k_499_);
lean_ctor_set(v_reuseFailAlloc_522_, 2, v_v_500_);
lean_ctor_set(v_reuseFailAlloc_522_, 3, v___y_514_);
lean_ctor_set(v_reuseFailAlloc_522_, 4, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
v___jp_524_:
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = lean_nat_add(v___x_511_, v___y_525_);
lean_dec(v___y_525_);
lean_dec(v___x_511_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v_l_501_);
lean_ctor_set(v___x_475_, 0, v___x_526_);
v___x_528_ = v___x_475_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_532_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_532_, 3, v_l_472_);
lean_ctor_set(v_reuseFailAlloc_532_, 4, v_l_501_);
v___x_528_ = v_reuseFailAlloc_532_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_529_; 
v___x_529_ = lean_nat_add(v___x_510_, v_size_503_);
if (lean_obj_tag(v_r_502_) == 0)
{
lean_object* v_size_530_; 
v_size_530_ = lean_ctor_get(v_r_502_, 0);
lean_inc(v_size_530_);
v___y_514_ = v___x_528_;
v___y_515_ = v___x_529_;
v___y_516_ = v_size_530_;
goto v___jp_513_;
}
else
{
lean_object* v___x_531_; 
v___x_531_ = lean_unsigned_to_nat(0u);
v___y_514_ = v___x_528_;
v___y_515_ = v___x_529_;
v___y_516_ = v___x_531_;
goto v___jp_513_;
}
}
}
}
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_546_; 
lean_del_object(v___x_475_);
v___x_541_ = lean_unsigned_to_nat(1u);
v___x_542_ = lean_nat_add(v___x_541_, v_size_480_);
v___x_543_ = lean_nat_add(v___x_542_, v_size_481_);
lean_dec(v_size_481_);
v___x_544_ = lean_nat_add(v___x_542_, v_size_498_);
lean_dec(v___x_542_);
lean_inc_ref(v_l_472_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 4, v_l_484_);
lean_ctor_set(v___x_496_, 3, v_l_472_);
lean_ctor_set(v___x_496_, 2, v_v_471_);
lean_ctor_set(v___x_496_, 1, v_k_470_);
lean_ctor_set(v___x_496_, 0, v___x_544_);
v___x_546_ = v___x_496_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_559_, 3, v_l_472_);
lean_ctor_set(v_reuseFailAlloc_559_, 4, v_l_484_);
v___x_546_ = v_reuseFailAlloc_559_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
v_isSharedCheck_553_ = !lean_is_exclusive(v_l_472_);
if (v_isSharedCheck_553_ == 0)
{
lean_object* v_unused_554_; lean_object* v_unused_555_; lean_object* v_unused_556_; lean_object* v_unused_557_; lean_object* v_unused_558_; 
v_unused_554_ = lean_ctor_get(v_l_472_, 4);
lean_dec(v_unused_554_);
v_unused_555_ = lean_ctor_get(v_l_472_, 3);
lean_dec(v_unused_555_);
v_unused_556_ = lean_ctor_get(v_l_472_, 2);
lean_dec(v_unused_556_);
v_unused_557_ = lean_ctor_get(v_l_472_, 1);
lean_dec(v_unused_557_);
v_unused_558_ = lean_ctor_get(v_l_472_, 0);
lean_dec(v_unused_558_);
v___x_548_ = v_l_472_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_dec(v_l_472_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 4, v_r_485_);
lean_ctor_set(v___x_548_, 3, v___x_546_);
lean_ctor_set(v___x_548_, 2, v_v_483_);
lean_ctor_set(v___x_548_, 1, v_k_482_);
lean_ctor_set(v___x_548_, 0, v___x_543_);
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_k_482_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v_v_483_);
lean_ctor_set(v_reuseFailAlloc_552_, 3, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_552_, 4, v_r_485_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec_ref(v_l_484_);
lean_del_object(v___x_496_);
lean_dec(v_v_483_);
lean_dec(v_k_482_);
lean_dec(v_size_481_);
lean_dec_ref(v_l_472_);
lean_del_object(v___x_475_);
lean_dec(v_v_471_);
lean_dec(v_k_470_);
v___x_560_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3);
v___x_561_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v___x_560_);
return v___x_561_;
}
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; 
lean_del_object(v___x_496_);
lean_dec(v_r_485_);
lean_dec(v_v_483_);
lean_dec(v_k_482_);
lean_dec(v_size_481_);
lean_dec_ref(v_l_472_);
lean_del_object(v___x_475_);
lean_dec(v_v_471_);
lean_dec(v_k_470_);
v___x_562_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4);
v___x_563_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v___x_562_);
return v___x_563_;
}
}
}
}
else
{
lean_object* v_size_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v_size_570_ = lean_ctor_get(v_l_472_, 0);
v___x_571_ = lean_unsigned_to_nat(1u);
v___x_572_ = lean_nat_add(v___x_571_, v_size_570_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v___x_479_);
lean_ctor_set(v___x_475_, 0, v___x_572_);
v___x_574_ = v___x_475_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_575_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_575_, 3, v_l_472_);
lean_ctor_set(v_reuseFailAlloc_575_, 4, v___x_479_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
else
{
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_l_576_; 
v_l_576_ = lean_ctor_get(v___x_479_, 3);
lean_inc(v_l_576_);
if (lean_obj_tag(v_l_576_) == 0)
{
lean_object* v_r_577_; 
v_r_577_ = lean_ctor_get(v___x_479_, 4);
lean_inc(v_r_577_);
if (lean_obj_tag(v_r_577_) == 0)
{
lean_object* v_size_578_; lean_object* v_k_579_; lean_object* v_v_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_594_; 
v_size_578_ = lean_ctor_get(v___x_479_, 0);
v_k_579_ = lean_ctor_get(v___x_479_, 1);
v_v_580_ = lean_ctor_get(v___x_479_, 2);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; lean_object* v_unused_596_; 
v_unused_595_ = lean_ctor_get(v___x_479_, 4);
lean_dec(v_unused_595_);
v_unused_596_ = lean_ctor_get(v___x_479_, 3);
lean_dec(v_unused_596_);
v___x_582_ = v___x_479_;
v_isShared_583_ = v_isSharedCheck_594_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_v_580_);
lean_inc(v_k_579_);
lean_inc(v_size_578_);
lean_dec(v___x_479_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_594_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v_size_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v_size_584_ = lean_ctor_get(v_l_576_, 0);
v___x_585_ = lean_unsigned_to_nat(1u);
v___x_586_ = lean_nat_add(v___x_585_, v_size_578_);
lean_dec(v_size_578_);
v___x_587_ = lean_nat_add(v___x_585_, v_size_584_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 4, v_l_576_);
lean_ctor_set(v___x_582_, 3, v_l_472_);
lean_ctor_set(v___x_582_, 2, v_v_471_);
lean_ctor_set(v___x_582_, 1, v_k_470_);
lean_ctor_set(v___x_582_, 0, v___x_587_);
v___x_589_ = v___x_582_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v_l_472_);
lean_ctor_set(v_reuseFailAlloc_593_, 4, v_l_576_);
v___x_589_ = v_reuseFailAlloc_593_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_591_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v_r_577_);
lean_ctor_set(v___x_475_, 3, v___x_589_);
lean_ctor_set(v___x_475_, 2, v_v_580_);
lean_ctor_set(v___x_475_, 1, v_k_579_);
lean_ctor_set(v___x_475_, 0, v___x_586_);
v___x_591_ = v___x_475_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_586_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_k_579_);
lean_ctor_set(v_reuseFailAlloc_592_, 2, v_v_580_);
lean_ctor_set(v_reuseFailAlloc_592_, 3, v___x_589_);
lean_ctor_set(v_reuseFailAlloc_592_, 4, v_r_577_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
else
{
lean_object* v_k_597_; lean_object* v_v_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_622_; 
v_k_597_ = lean_ctor_get(v___x_479_, 1);
v_v_598_ = lean_ctor_get(v___x_479_, 2);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; lean_object* v_unused_624_; lean_object* v_unused_625_; 
v_unused_623_ = lean_ctor_get(v___x_479_, 4);
lean_dec(v_unused_623_);
v_unused_624_ = lean_ctor_get(v___x_479_, 3);
lean_dec(v_unused_624_);
v_unused_625_ = lean_ctor_get(v___x_479_, 0);
lean_dec(v_unused_625_);
v___x_600_ = v___x_479_;
v_isShared_601_ = v_isSharedCheck_622_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_v_598_);
lean_inc(v_k_597_);
lean_dec(v___x_479_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_622_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v_k_602_; lean_object* v_v_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_618_; 
v_k_602_ = lean_ctor_get(v_l_576_, 1);
v_v_603_ = lean_ctor_get(v_l_576_, 2);
v_isSharedCheck_618_ = !lean_is_exclusive(v_l_576_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; lean_object* v_unused_620_; lean_object* v_unused_621_; 
v_unused_619_ = lean_ctor_get(v_l_576_, 4);
lean_dec(v_unused_619_);
v_unused_620_ = lean_ctor_get(v_l_576_, 3);
lean_dec(v_unused_620_);
v_unused_621_ = lean_ctor_get(v_l_576_, 0);
lean_dec(v_unused_621_);
v___x_605_ = v_l_576_;
v_isShared_606_ = v_isSharedCheck_618_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_v_603_);
lean_inc(v_k_602_);
lean_dec(v_l_576_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_618_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_607_ = lean_unsigned_to_nat(3u);
v___x_608_ = lean_unsigned_to_nat(1u);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 4, v_r_577_);
lean_ctor_set(v___x_605_, 3, v_r_577_);
lean_ctor_set(v___x_605_, 2, v_v_471_);
lean_ctor_set(v___x_605_, 1, v_k_470_);
lean_ctor_set(v___x_605_, 0, v___x_608_);
v___x_610_ = v___x_605_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v_r_577_);
lean_ctor_set(v_reuseFailAlloc_617_, 4, v_r_577_);
v___x_610_ = v_reuseFailAlloc_617_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_612_; 
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 3, v_r_577_);
lean_ctor_set(v___x_600_, 0, v___x_608_);
v___x_612_ = v___x_600_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_k_597_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_v_598_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v_r_577_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v_r_577_);
v___x_612_ = v_reuseFailAlloc_616_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_614_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v___x_612_);
lean_ctor_set(v___x_475_, 3, v___x_610_);
lean_ctor_set(v___x_475_, 2, v_v_603_);
lean_ctor_set(v___x_475_, 1, v_k_602_);
lean_ctor_set(v___x_475_, 0, v___x_607_);
v___x_614_ = v___x_475_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_k_602_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_v_603_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v___x_610_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v___x_612_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_626_; 
v_r_626_ = lean_ctor_get(v___x_479_, 4);
lean_inc(v_r_626_);
if (lean_obj_tag(v_r_626_) == 0)
{
lean_object* v_k_627_; lean_object* v_v_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_640_; 
v_k_627_ = lean_ctor_get(v___x_479_, 1);
v_v_628_ = lean_ctor_get(v___x_479_, 2);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; lean_object* v_unused_642_; lean_object* v_unused_643_; 
v_unused_641_ = lean_ctor_get(v___x_479_, 4);
lean_dec(v_unused_641_);
v_unused_642_ = lean_ctor_get(v___x_479_, 3);
lean_dec(v_unused_642_);
v_unused_643_ = lean_ctor_get(v___x_479_, 0);
lean_dec(v_unused_643_);
v___x_630_ = v___x_479_;
v_isShared_631_ = v_isSharedCheck_640_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_v_628_);
lean_inc(v_k_627_);
lean_dec(v___x_479_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_640_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_632_ = lean_unsigned_to_nat(3u);
v___x_633_ = lean_unsigned_to_nat(1u);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 4, v_l_576_);
lean_ctor_set(v___x_630_, 2, v_v_471_);
lean_ctor_set(v___x_630_, 1, v_k_470_);
lean_ctor_set(v___x_630_, 0, v___x_633_);
v___x_635_ = v___x_630_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_639_, 3, v_l_576_);
lean_ctor_set(v_reuseFailAlloc_639_, 4, v_l_576_);
v___x_635_ = v_reuseFailAlloc_639_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_637_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v_r_626_);
lean_ctor_set(v___x_475_, 3, v___x_635_);
lean_ctor_set(v___x_475_, 2, v_v_628_);
lean_ctor_set(v___x_475_, 1, v_k_627_);
lean_ctor_set(v___x_475_, 0, v___x_632_);
v___x_637_ = v___x_475_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_k_627_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_v_628_);
lean_ctor_set(v_reuseFailAlloc_638_, 3, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_638_, 4, v_r_626_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
else
{
lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_644_ = lean_unsigned_to_nat(2u);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v___x_479_);
lean_ctor_set(v___x_475_, 3, v_r_626_);
lean_ctor_set(v___x_475_, 0, v___x_644_);
v___x_646_ = v___x_475_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_647_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_647_, 3, v_r_626_);
lean_ctor_set(v_reuseFailAlloc_647_, 4, v___x_479_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
else
{
lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_648_ = lean_unsigned_to_nat(1u);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v___x_479_);
lean_ctor_set(v___x_475_, 3, v___x_479_);
lean_ctor_set(v___x_475_, 0, v___x_648_);
v___x_650_ = v___x_475_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_651_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_651_, 3, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_651_, 4, v___x_479_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
lean_object* v___x_653_; 
lean_dec(v_v_471_);
lean_dec(v_k_470_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 2, v_v_467_);
lean_ctor_set(v___x_475_, 1, v_k_466_);
v___x_653_ = v___x_475_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_size_469_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_k_466_);
lean_ctor_set(v_reuseFailAlloc_654_, 2, v_v_467_);
lean_ctor_set(v_reuseFailAlloc_654_, 3, v_l_472_);
lean_ctor_set(v_reuseFailAlloc_654_, 4, v_r_473_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
else
{
lean_object* v___x_655_; 
lean_dec(v_size_469_);
v___x_655_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(v_k_466_, v_v_467_, v_l_472_);
if (lean_obj_tag(v_r_473_) == 0)
{
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_size_656_; lean_object* v_size_657_; lean_object* v_k_658_; lean_object* v_v_659_; lean_object* v_l_660_; lean_object* v_r_661_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v_size_656_ = lean_ctor_get(v_r_473_, 0);
v_size_657_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_size_657_);
v_k_658_ = lean_ctor_get(v___x_655_, 1);
lean_inc(v_k_658_);
v_v_659_ = lean_ctor_get(v___x_655_, 2);
lean_inc(v_v_659_);
v_l_660_ = lean_ctor_get(v___x_655_, 3);
lean_inc(v_l_660_);
v_r_661_ = lean_ctor_get(v___x_655_, 4);
lean_inc(v_r_661_);
v___x_662_ = lean_unsigned_to_nat(3u);
v___x_663_ = lean_nat_mul(v___x_662_, v_size_656_);
v___x_664_ = lean_nat_dec_lt(v___x_663_, v_size_657_);
lean_dec(v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_669_; 
lean_dec(v_r_661_);
lean_dec(v_l_660_);
lean_dec(v_v_659_);
lean_dec(v_k_658_);
v___x_665_ = lean_unsigned_to_nat(1u);
v___x_666_ = lean_nat_add(v___x_665_, v_size_657_);
lean_dec(v_size_657_);
v___x_667_ = lean_nat_add(v___x_666_, v_size_656_);
lean_dec(v___x_666_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 3, v___x_655_);
lean_ctor_set(v___x_475_, 0, v___x_667_);
v___x_669_ = v___x_475_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_670_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_670_, 3, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_670_, 4, v_r_473_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
else
{
lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_742_; 
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; lean_object* v_unused_744_; lean_object* v_unused_745_; lean_object* v_unused_746_; lean_object* v_unused_747_; 
v_unused_743_ = lean_ctor_get(v___x_655_, 4);
lean_dec(v_unused_743_);
v_unused_744_ = lean_ctor_get(v___x_655_, 3);
lean_dec(v_unused_744_);
v_unused_745_ = lean_ctor_get(v___x_655_, 2);
lean_dec(v_unused_745_);
v_unused_746_ = lean_ctor_get(v___x_655_, 1);
lean_dec(v_unused_746_);
v_unused_747_ = lean_ctor_get(v___x_655_, 0);
lean_dec(v_unused_747_);
v___x_672_ = v___x_655_;
v_isShared_673_ = v_isSharedCheck_742_;
goto v_resetjp_671_;
}
else
{
lean_dec(v___x_655_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_742_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
if (lean_obj_tag(v_l_660_) == 0)
{
if (lean_obj_tag(v_r_661_) == 0)
{
lean_object* v_size_674_; lean_object* v_size_675_; lean_object* v_k_676_; lean_object* v_v_677_; lean_object* v_l_678_; lean_object* v_r_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v_size_674_ = lean_ctor_get(v_l_660_, 0);
v_size_675_ = lean_ctor_get(v_r_661_, 0);
v_k_676_ = lean_ctor_get(v_r_661_, 1);
v_v_677_ = lean_ctor_get(v_r_661_, 2);
v_l_678_ = lean_ctor_get(v_r_661_, 3);
v_r_679_ = lean_ctor_get(v_r_661_, 4);
v___x_680_ = lean_unsigned_to_nat(2u);
v___x_681_ = lean_nat_mul(v___x_680_, v_size_674_);
v___x_682_ = lean_nat_dec_lt(v_size_675_, v___x_681_);
lean_dec(v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_712_; 
lean_inc(v_r_679_);
lean_inc(v_l_678_);
lean_inc(v_v_677_);
lean_inc(v_k_676_);
v_isSharedCheck_712_ = !lean_is_exclusive(v_r_661_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; lean_object* v_unused_714_; lean_object* v_unused_715_; lean_object* v_unused_716_; lean_object* v_unused_717_; 
v_unused_713_ = lean_ctor_get(v_r_661_, 4);
lean_dec(v_unused_713_);
v_unused_714_ = lean_ctor_get(v_r_661_, 3);
lean_dec(v_unused_714_);
v_unused_715_ = lean_ctor_get(v_r_661_, 2);
lean_dec(v_unused_715_);
v_unused_716_ = lean_ctor_get(v_r_661_, 1);
lean_dec(v_unused_716_);
v_unused_717_ = lean_ctor_get(v_r_661_, 0);
lean_dec(v_unused_717_);
v___x_684_ = v_r_661_;
v_isShared_685_ = v_isSharedCheck_712_;
goto v_resetjp_683_;
}
else
{
lean_dec(v_r_661_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_712_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___x_700_; lean_object* v___y_702_; 
v___x_686_ = lean_unsigned_to_nat(1u);
v___x_687_ = lean_nat_add(v___x_686_, v_size_657_);
lean_dec(v_size_657_);
v___x_688_ = lean_nat_add(v___x_687_, v_size_656_);
lean_dec(v___x_687_);
v___x_700_ = lean_nat_add(v___x_686_, v_size_674_);
if (lean_obj_tag(v_l_678_) == 0)
{
lean_object* v_size_710_; 
v_size_710_ = lean_ctor_get(v_l_678_, 0);
lean_inc(v_size_710_);
v___y_702_ = v_size_710_;
goto v___jp_701_;
}
else
{
lean_object* v___x_711_; 
v___x_711_ = lean_unsigned_to_nat(0u);
v___y_702_ = v___x_711_;
goto v___jp_701_;
}
v___jp_689_:
{
lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_693_ = lean_nat_add(v___y_690_, v___y_692_);
lean_dec(v___y_692_);
lean_dec(v___y_690_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 4, v_r_473_);
lean_ctor_set(v___x_684_, 3, v_r_679_);
lean_ctor_set(v___x_684_, 2, v_v_471_);
lean_ctor_set(v___x_684_, 1, v_k_470_);
lean_ctor_set(v___x_684_, 0, v___x_693_);
v___x_695_ = v___x_684_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_699_, 3, v_r_679_);
lean_ctor_set(v_reuseFailAlloc_699_, 4, v_r_473_);
v___x_695_ = v_reuseFailAlloc_699_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_697_; 
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 4, v___x_695_);
lean_ctor_set(v___x_672_, 3, v___y_691_);
lean_ctor_set(v___x_672_, 2, v_v_677_);
lean_ctor_set(v___x_672_, 1, v_k_676_);
lean_ctor_set(v___x_672_, 0, v___x_688_);
v___x_697_ = v___x_672_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_k_676_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v_v_677_);
lean_ctor_set(v_reuseFailAlloc_698_, 3, v___y_691_);
lean_ctor_set(v_reuseFailAlloc_698_, 4, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
v___jp_701_:
{
lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_703_ = lean_nat_add(v___x_700_, v___y_702_);
lean_dec(v___y_702_);
lean_dec(v___x_700_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v_l_678_);
lean_ctor_set(v___x_475_, 3, v_l_660_);
lean_ctor_set(v___x_475_, 2, v_v_659_);
lean_ctor_set(v___x_475_, 1, v_k_658_);
lean_ctor_set(v___x_475_, 0, v___x_703_);
v___x_705_ = v___x_475_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_k_658_);
lean_ctor_set(v_reuseFailAlloc_709_, 2, v_v_659_);
lean_ctor_set(v_reuseFailAlloc_709_, 3, v_l_660_);
lean_ctor_set(v_reuseFailAlloc_709_, 4, v_l_678_);
v___x_705_ = v_reuseFailAlloc_709_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_706_; 
v___x_706_ = lean_nat_add(v___x_686_, v_size_656_);
if (lean_obj_tag(v_r_679_) == 0)
{
lean_object* v_size_707_; 
v_size_707_ = lean_ctor_get(v_r_679_, 0);
lean_inc(v_size_707_);
v___y_690_ = v___x_706_;
v___y_691_ = v___x_705_;
v___y_692_ = v_size_707_;
goto v___jp_689_;
}
else
{
lean_object* v___x_708_; 
v___x_708_ = lean_unsigned_to_nat(0u);
v___y_690_ = v___x_706_;
v___y_691_ = v___x_705_;
v___y_692_ = v___x_708_;
goto v___jp_689_;
}
}
}
}
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
lean_del_object(v___x_475_);
v___x_718_ = lean_unsigned_to_nat(1u);
v___x_719_ = lean_nat_add(v___x_718_, v_size_657_);
lean_dec(v_size_657_);
v___x_720_ = lean_nat_add(v___x_719_, v_size_656_);
lean_dec(v___x_719_);
v___x_721_ = lean_nat_add(v___x_718_, v_size_656_);
v___x_722_ = lean_nat_add(v___x_721_, v_size_675_);
lean_dec(v___x_721_);
lean_inc_ref(v_r_473_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 4, v_r_473_);
lean_ctor_set(v___x_672_, 3, v_r_661_);
lean_ctor_set(v___x_672_, 2, v_v_471_);
lean_ctor_set(v___x_672_, 1, v_k_470_);
lean_ctor_set(v___x_672_, 0, v___x_722_);
v___x_724_ = v___x_672_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_737_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_737_, 3, v_r_661_);
lean_ctor_set(v_reuseFailAlloc_737_, 4, v_r_473_);
v___x_724_ = v_reuseFailAlloc_737_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
v_isSharedCheck_731_ = !lean_is_exclusive(v_r_473_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; lean_object* v_unused_733_; lean_object* v_unused_734_; lean_object* v_unused_735_; lean_object* v_unused_736_; 
v_unused_732_ = lean_ctor_get(v_r_473_, 4);
lean_dec(v_unused_732_);
v_unused_733_ = lean_ctor_get(v_r_473_, 3);
lean_dec(v_unused_733_);
v_unused_734_ = lean_ctor_get(v_r_473_, 2);
lean_dec(v_unused_734_);
v_unused_735_ = lean_ctor_get(v_r_473_, 1);
lean_dec(v_unused_735_);
v_unused_736_ = lean_ctor_get(v_r_473_, 0);
lean_dec(v_unused_736_);
v___x_726_ = v_r_473_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_dec(v_r_473_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 4, v___x_724_);
lean_ctor_set(v___x_726_, 3, v_l_660_);
lean_ctor_set(v___x_726_, 2, v_v_659_);
lean_ctor_set(v___x_726_, 1, v_k_658_);
lean_ctor_set(v___x_726_, 0, v___x_720_);
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_k_658_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_v_659_);
lean_ctor_set(v_reuseFailAlloc_730_, 3, v_l_660_);
lean_ctor_set(v_reuseFailAlloc_730_, 4, v___x_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; 
lean_dec_ref(v_l_660_);
lean_del_object(v___x_672_);
lean_dec(v_v_659_);
lean_dec(v_k_658_);
lean_dec(v_size_657_);
lean_dec_ref(v_r_473_);
lean_del_object(v___x_475_);
lean_dec(v_v_471_);
lean_dec(v_k_470_);
v___x_738_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7);
v___x_739_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v___x_738_);
return v___x_739_;
}
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; 
lean_del_object(v___x_672_);
lean_dec(v_r_661_);
lean_dec(v_v_659_);
lean_dec(v_k_658_);
lean_dec(v_size_657_);
lean_dec_ref(v_r_473_);
lean_del_object(v___x_475_);
lean_dec(v_v_471_);
lean_dec(v_k_470_);
v___x_740_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8);
v___x_741_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v___x_740_);
return v___x_741_;
}
}
}
}
else
{
lean_object* v_size_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_752_; 
v_size_748_ = lean_ctor_get(v_r_473_, 0);
v___x_749_ = lean_unsigned_to_nat(1u);
v___x_750_ = lean_nat_add(v___x_749_, v_size_748_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 3, v___x_655_);
lean_ctor_set(v___x_475_, 0, v___x_750_);
v___x_752_ = v___x_475_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_753_, 3, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_753_, 4, v_r_473_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
else
{
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_l_754_; 
v_l_754_ = lean_ctor_get(v___x_655_, 3);
lean_inc(v_l_754_);
if (lean_obj_tag(v_l_754_) == 0)
{
lean_object* v_r_755_; 
v_r_755_ = lean_ctor_get(v___x_655_, 4);
lean_inc(v_r_755_);
if (lean_obj_tag(v_r_755_) == 0)
{
lean_object* v_size_756_; lean_object* v_k_757_; lean_object* v_v_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_772_; 
v_size_756_ = lean_ctor_get(v___x_655_, 0);
v_k_757_ = lean_ctor_get(v___x_655_, 1);
v_v_758_ = lean_ctor_get(v___x_655_, 2);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_772_ == 0)
{
lean_object* v_unused_773_; lean_object* v_unused_774_; 
v_unused_773_ = lean_ctor_get(v___x_655_, 4);
lean_dec(v_unused_773_);
v_unused_774_ = lean_ctor_get(v___x_655_, 3);
lean_dec(v_unused_774_);
v___x_760_ = v___x_655_;
v_isShared_761_ = v_isSharedCheck_772_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_v_758_);
lean_inc(v_k_757_);
lean_inc(v_size_756_);
lean_dec(v___x_655_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_772_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v_size_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_767_; 
v_size_762_ = lean_ctor_get(v_r_755_, 0);
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = lean_nat_add(v___x_763_, v_size_756_);
lean_dec(v_size_756_);
v___x_765_ = lean_nat_add(v___x_763_, v_size_762_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 4, v_r_473_);
lean_ctor_set(v___x_760_, 3, v_r_755_);
lean_ctor_set(v___x_760_, 2, v_v_471_);
lean_ctor_set(v___x_760_, 1, v_k_470_);
lean_ctor_set(v___x_760_, 0, v___x_765_);
v___x_767_ = v___x_760_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_771_, 3, v_r_755_);
lean_ctor_set(v_reuseFailAlloc_771_, 4, v_r_473_);
v___x_767_ = v_reuseFailAlloc_771_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v___x_767_);
lean_ctor_set(v___x_475_, 3, v_l_754_);
lean_ctor_set(v___x_475_, 2, v_v_758_);
lean_ctor_set(v___x_475_, 1, v_k_757_);
lean_ctor_set(v___x_475_, 0, v___x_764_);
v___x_769_ = v___x_475_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_k_757_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_v_758_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v_l_754_);
lean_ctor_set(v_reuseFailAlloc_770_, 4, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
else
{
lean_object* v_k_775_; lean_object* v_v_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_788_; 
v_k_775_ = lean_ctor_get(v___x_655_, 1);
v_v_776_ = lean_ctor_get(v___x_655_, 2);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; lean_object* v_unused_790_; lean_object* v_unused_791_; 
v_unused_789_ = lean_ctor_get(v___x_655_, 4);
lean_dec(v_unused_789_);
v_unused_790_ = lean_ctor_get(v___x_655_, 3);
lean_dec(v_unused_790_);
v_unused_791_ = lean_ctor_get(v___x_655_, 0);
lean_dec(v_unused_791_);
v___x_778_ = v___x_655_;
v_isShared_779_ = v_isSharedCheck_788_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_v_776_);
lean_inc(v_k_775_);
lean_dec(v___x_655_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_788_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_780_ = lean_unsigned_to_nat(3u);
v___x_781_ = lean_unsigned_to_nat(1u);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 3, v_r_755_);
lean_ctor_set(v___x_778_, 2, v_v_471_);
lean_ctor_set(v___x_778_, 1, v_k_470_);
lean_ctor_set(v___x_778_, 0, v___x_781_);
v___x_783_ = v___x_778_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_787_, 3, v_r_755_);
lean_ctor_set(v_reuseFailAlloc_787_, 4, v_r_755_);
v___x_783_ = v_reuseFailAlloc_787_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_785_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v___x_783_);
lean_ctor_set(v___x_475_, 3, v_l_754_);
lean_ctor_set(v___x_475_, 2, v_v_776_);
lean_ctor_set(v___x_475_, 1, v_k_775_);
lean_ctor_set(v___x_475_, 0, v___x_780_);
v___x_785_ = v___x_475_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_k_775_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v_v_776_);
lean_ctor_set(v_reuseFailAlloc_786_, 3, v_l_754_);
lean_ctor_set(v_reuseFailAlloc_786_, 4, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
else
{
lean_object* v_r_792_; 
v_r_792_ = lean_ctor_get(v___x_655_, 4);
lean_inc(v_r_792_);
if (lean_obj_tag(v_r_792_) == 0)
{
lean_object* v_k_793_; lean_object* v_v_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_818_; 
v_k_793_ = lean_ctor_get(v___x_655_, 1);
v_v_794_ = lean_ctor_get(v___x_655_, 2);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; lean_object* v_unused_820_; lean_object* v_unused_821_; 
v_unused_819_ = lean_ctor_get(v___x_655_, 4);
lean_dec(v_unused_819_);
v_unused_820_ = lean_ctor_get(v___x_655_, 3);
lean_dec(v_unused_820_);
v_unused_821_ = lean_ctor_get(v___x_655_, 0);
lean_dec(v_unused_821_);
v___x_796_ = v___x_655_;
v_isShared_797_ = v_isSharedCheck_818_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_v_794_);
lean_inc(v_k_793_);
lean_dec(v___x_655_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_818_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v_k_798_; lean_object* v_v_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_814_; 
v_k_798_ = lean_ctor_get(v_r_792_, 1);
v_v_799_ = lean_ctor_get(v_r_792_, 2);
v_isSharedCheck_814_ = !lean_is_exclusive(v_r_792_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; lean_object* v_unused_816_; lean_object* v_unused_817_; 
v_unused_815_ = lean_ctor_get(v_r_792_, 4);
lean_dec(v_unused_815_);
v_unused_816_ = lean_ctor_get(v_r_792_, 3);
lean_dec(v_unused_816_);
v_unused_817_ = lean_ctor_get(v_r_792_, 0);
lean_dec(v_unused_817_);
v___x_801_ = v_r_792_;
v_isShared_802_ = v_isSharedCheck_814_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_v_799_);
lean_inc(v_k_798_);
lean_dec(v_r_792_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_814_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_803_ = lean_unsigned_to_nat(3u);
v___x_804_ = lean_unsigned_to_nat(1u);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 4, v_l_754_);
lean_ctor_set(v___x_801_, 3, v_l_754_);
lean_ctor_set(v___x_801_, 2, v_v_794_);
lean_ctor_set(v___x_801_, 1, v_k_793_);
lean_ctor_set(v___x_801_, 0, v___x_804_);
v___x_806_ = v___x_801_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_804_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_k_793_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_v_794_);
lean_ctor_set(v_reuseFailAlloc_813_, 3, v_l_754_);
lean_ctor_set(v_reuseFailAlloc_813_, 4, v_l_754_);
v___x_806_ = v_reuseFailAlloc_813_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_808_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 4, v_l_754_);
lean_ctor_set(v___x_796_, 2, v_v_471_);
lean_ctor_set(v___x_796_, 1, v_k_470_);
lean_ctor_set(v___x_796_, 0, v___x_804_);
v___x_808_ = v___x_796_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_804_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_812_, 3, v_l_754_);
lean_ctor_set(v_reuseFailAlloc_812_, 4, v_l_754_);
v___x_808_ = v_reuseFailAlloc_812_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_810_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v___x_808_);
lean_ctor_set(v___x_475_, 3, v___x_806_);
lean_ctor_set(v___x_475_, 2, v_v_799_);
lean_ctor_set(v___x_475_, 1, v_k_798_);
lean_ctor_set(v___x_475_, 0, v___x_803_);
v___x_810_ = v___x_475_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_k_798_);
lean_ctor_set(v_reuseFailAlloc_811_, 2, v_v_799_);
lean_ctor_set(v_reuseFailAlloc_811_, 3, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_811_, 4, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
}
else
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = lean_unsigned_to_nat(2u);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v_r_792_);
lean_ctor_set(v___x_475_, 3, v___x_655_);
lean_ctor_set(v___x_475_, 0, v___x_822_);
v___x_824_ = v___x_475_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_825_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_825_, 3, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_825_, 4, v_r_792_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_826_ = lean_unsigned_to_nat(1u);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v___x_655_);
lean_ctor_set(v___x_475_, 3, v___x_655_);
lean_ctor_set(v___x_475_, 0, v___x_826_);
v___x_828_ = v___x_475_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_829_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_829_, 3, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_829_, 4, v___x_655_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
}
else
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_unsigned_to_nat(1u);
v___x_832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v_k_466_);
lean_ctor_set(v___x_832_, 2, v_v_467_);
lean_ctor_set(v___x_832_, 3, v_t_468_);
lean_ctor_set(v___x_832_, 4, v_t_468_);
return v___x_832_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1_spec__5(lean_object* v_init_833_, lean_object* v_x_834_){
_start:
{
if (lean_obj_tag(v_x_834_) == 0)
{
lean_object* v_k_835_; lean_object* v_v_836_; lean_object* v_l_837_; lean_object* v_r_838_; lean_object* v___x_839_; uint8_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_k_835_ = lean_ctor_get(v_x_834_, 1);
lean_inc(v_k_835_);
v_v_836_ = lean_ctor_get(v_x_834_, 2);
lean_inc(v_v_836_);
v_l_837_ = lean_ctor_get(v_x_834_, 3);
lean_inc(v_l_837_);
v_r_838_ = lean_ctor_get(v_x_834_, 4);
lean_inc(v_r_838_);
lean_dec_ref(v_x_834_);
v___x_839_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1_spec__5(v_init_833_, v_l_837_);
v___x_840_ = 1;
v___x_841_ = l_Lean_Name_toString(v_k_835_, v___x_840_);
v___x_842_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_842_, 0, v_v_836_);
v___x_843_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(v___x_841_, v___x_842_, v___x_839_);
v_init_833_ = v___x_843_;
v_x_834_ = v_r_838_;
goto _start;
}
else
{
return v_init_833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0(lean_object* v_m_845_){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_846_ = lean_box(1);
v___x_847_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1_spec__5(v___x_846_, v_m_845_);
v___x_848_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson(lean_object* v_x_849_){
_start:
{
if (lean_obj_tag(v_x_849_) == 0)
{
lean_object* v_name_850_; lean_object* v_opts_851_; uint8_t v_inherited_852_; lean_object* v_dir_853_; lean_object* v___x_854_; lean_object* v___x_855_; uint8_t v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_name_850_ = lean_ctor_get(v_x_849_, 0);
lean_inc(v_name_850_);
v_opts_851_ = lean_ctor_get(v_x_849_, 1);
lean_inc(v_opts_851_);
v_inherited_852_ = lean_ctor_get_uint8(v_x_849_, sizeof(void*)*3);
v_dir_853_ = lean_ctor_get(v_x_849_, 2);
lean_inc_ref(v_dir_853_);
lean_dec_ref(v_x_849_);
v___x_854_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2));
v___x_855_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_856_ = 1;
v___x_857_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_850_, v___x_856_);
v___x_858_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_855_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__8));
v___x_861_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0(v_opts_851_);
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10));
v___x_864_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_864_, 0, v_inherited_852_);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_863_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22));
v___x_867_ = l_Lake_mkRelPathString(v_dir_853_);
v___x_868_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_866_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = lean_box(0);
v___x_871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_869_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_865_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_862_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_859_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = l_Lean_Json_mkObj(v___x_874_);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_854_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
lean_ctor_set(v___x_877_, 1, v___x_870_);
v___x_878_ = l_Lean_Json_mkObj(v___x_877_);
return v___x_878_;
}
else
{
lean_object* v_name_879_; lean_object* v_opts_880_; uint8_t v_inherited_881_; lean_object* v_url_882_; lean_object* v_rev_883_; lean_object* v_inputRev_x3f_884_; lean_object* v_subDir_x3f_885_; lean_object* v___x_886_; lean_object* v___x_887_; uint8_t v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v_name_879_ = lean_ctor_get(v_x_849_, 0);
lean_inc(v_name_879_);
v_opts_880_ = lean_ctor_get(v_x_849_, 1);
lean_inc(v_opts_880_);
v_inherited_881_ = lean_ctor_get_uint8(v_x_849_, sizeof(void*)*6);
v_url_882_ = lean_ctor_get(v_x_849_, 2);
lean_inc_ref(v_url_882_);
v_rev_883_ = lean_ctor_get(v_x_849_, 3);
lean_inc_ref(v_rev_883_);
v_inputRev_x3f_884_ = lean_ctor_get(v_x_849_, 4);
lean_inc(v_inputRev_x3f_884_);
v_subDir_x3f_885_ = lean_ctor_get(v_x_849_, 5);
lean_inc(v_subDir_x3f_885_);
lean_dec_ref(v_x_849_);
v___x_886_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3));
v___x_887_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_888_ = 1;
v___x_889_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_879_, v___x_888_);
v___x_890_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_887_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__8));
v___x_893_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0(v_opts_880_);
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10));
v___x_896_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_896_, 0, v_inherited_881_);
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12));
v___x_899_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_899_, 0, v_url_882_);
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14));
v___x_902_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_902_, 0, v_rev_883_);
v___x_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__16));
v___x_905_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__1(v_inputRev_x3f_884_);
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__18));
v___x_908_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_subDir_x3f_885_);
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_box(0);
v___x_911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_906_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_903_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_900_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_897_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_894_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_891_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = l_Lean_Json_mkObj(v___x_917_);
v___x_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_886_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
lean_ctor_set(v___x_920_, 1, v___x_910_);
v___x_921_ = l_Lean_Json_mkObj(v___x_920_);
return v___x_921_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_922_, lean_object* v_msg_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v_msg_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0(lean_object* v_00_u03b2_925_, lean_object* v_k_926_, lean_object* v_v_927_, lean_object* v_t_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(v_k_926_, v_v_927_, v_t_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1(lean_object* v_init_930_, lean_object* v_t_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1_spec__5(v_init_930_, v_t_931_);
return v___x_932_;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6_default___closed__0(void){
_start:
{
lean_object* v___x_935_; uint8_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_935_ = l_System_instInhabitedFilePath_default;
v___x_936_ = 0;
v___x_937_ = lean_box(1);
v___x_938_ = lean_box(0);
v___x_939_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v___x_937_);
lean_ctor_set(v___x_939_, 2, v___x_935_);
lean_ctor_set_uint8(v___x_939_, sizeof(void*)*3, v___x_936_);
return v___x_939_;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6_default(void){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = lean_obj_once(&l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6_default___closed__0, &l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6_default___closed__0_once, _init_l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6_default___closed__0);
return v___x_940_;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6(void){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6_default;
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorIdx(lean_object* v_x_942_){
_start:
{
if (lean_obj_tag(v_x_942_) == 0)
{
lean_object* v___x_943_; 
v___x_943_ = lean_unsigned_to_nat(0u);
return v___x_943_;
}
else
{
lean_object* v___x_944_; 
v___x_944_ = lean_unsigned_to_nat(1u);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorIdx___boxed(lean_object* v_x_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lake_PackageEntrySrc_ctorIdx(v_x_945_);
lean_dec_ref(v_x_945_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorElim___redArg(lean_object* v_t_947_, lean_object* v_k_948_){
_start:
{
if (lean_obj_tag(v_t_947_) == 0)
{
lean_object* v_dir_949_; lean_object* v___x_950_; 
v_dir_949_ = lean_ctor_get(v_t_947_, 0);
lean_inc_ref(v_dir_949_);
lean_dec_ref(v_t_947_);
v___x_950_ = lean_apply_1(v_k_948_, v_dir_949_);
return v___x_950_;
}
else
{
lean_object* v_url_951_; lean_object* v_rev_952_; lean_object* v_inputRev_x3f_953_; lean_object* v_subDir_x3f_954_; lean_object* v___x_955_; 
v_url_951_ = lean_ctor_get(v_t_947_, 0);
lean_inc_ref(v_url_951_);
v_rev_952_ = lean_ctor_get(v_t_947_, 1);
lean_inc_ref(v_rev_952_);
v_inputRev_x3f_953_ = lean_ctor_get(v_t_947_, 2);
lean_inc(v_inputRev_x3f_953_);
v_subDir_x3f_954_ = lean_ctor_get(v_t_947_, 3);
lean_inc(v_subDir_x3f_954_);
lean_dec_ref(v_t_947_);
v___x_955_ = lean_apply_4(v_k_948_, v_url_951_, v_rev_952_, v_inputRev_x3f_953_, v_subDir_x3f_954_);
return v___x_955_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorElim(lean_object* v_motive_956_, lean_object* v_ctorIdx_957_, lean_object* v_t_958_, lean_object* v_h_959_, lean_object* v_k_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_958_, v_k_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorElim___boxed(lean_object* v_motive_962_, lean_object* v_ctorIdx_963_, lean_object* v_t_964_, lean_object* v_h_965_, lean_object* v_k_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lake_PackageEntrySrc_ctorElim(v_motive_962_, v_ctorIdx_963_, v_t_964_, v_h_965_, v_k_966_);
lean_dec(v_ctorIdx_963_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_path_elim___redArg(lean_object* v_t_968_, lean_object* v_path_969_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_968_, v_path_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_path_elim(lean_object* v_motive_971_, lean_object* v_t_972_, lean_object* v_h_973_, lean_object* v_path_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_972_, v_path_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_git_elim___redArg(lean_object* v_t_976_, lean_object* v_git_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_976_, v_git_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_git_elim(lean_object* v_motive_979_, lean_object* v_t_980_, lean_object* v_h_981_, lean_object* v_git_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_980_, v_git_982_);
return v___x_983_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntrySrc_default___closed__0(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = l_System_instInhabitedFilePath_default;
v___x_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
return v___x_985_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntrySrc_default(void){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = lean_obj_once(&l_Lake_instInhabitedPackageEntrySrc_default___closed__0, &l_Lake_instInhabitedPackageEntrySrc_default___closed__0_once, _init_l_Lake_instInhabitedPackageEntrySrc_default___closed__0);
return v___x_986_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntrySrc(void){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lake_instInhabitedPackageEntrySrc_default;
return v___x_987_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntry_default___closed__0(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_988_ = l_Lake_instInhabitedPackageEntrySrc_default;
v___x_989_ = lean_box(0);
v___x_990_ = l_System_instInhabitedFilePath_default;
v___x_991_ = 0;
v___x_992_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_993_ = lean_box(0);
v___x_994_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set(v___x_994_, 1, v___x_992_);
lean_ctor_set(v___x_994_, 2, v___x_990_);
lean_ctor_set(v___x_994_, 3, v___x_989_);
lean_ctor_set(v___x_994_, 4, v___x_988_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*5, v___x_991_);
return v___x_994_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntry_default(void){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = lean_obj_once(&l_Lake_instInhabitedPackageEntry_default___closed__0, &l_Lake_instInhabitedPackageEntry_default___closed__0_once, _init_l_Lake_instInhabitedPackageEntry_default___closed__0);
return v___x_995_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntry(void){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Lake_instInhabitedPackageEntry_default;
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_toJson(lean_object* v_entry_1013_){
_start:
{
lean_object* v_name_1014_; lean_object* v_scope_1015_; uint8_t v_inherited_1016_; lean_object* v_configFile_1017_; lean_object* v_manifestFile_x3f_1018_; lean_object* v_src_1019_; lean_object* v___x_1020_; uint8_t v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v_fields_1043_; 
v_name_1014_ = lean_ctor_get(v_entry_1013_, 0);
lean_inc(v_name_1014_);
v_scope_1015_ = lean_ctor_get(v_entry_1013_, 1);
lean_inc_ref(v_scope_1015_);
v_inherited_1016_ = lean_ctor_get_uint8(v_entry_1013_, sizeof(void*)*5);
v_configFile_1017_ = lean_ctor_get(v_entry_1013_, 2);
lean_inc_ref(v_configFile_1017_);
v_manifestFile_x3f_1018_ = lean_ctor_get(v_entry_1013_, 3);
lean_inc(v_manifestFile_x3f_1018_);
v_src_1019_ = lean_ctor_get(v_entry_1013_, 4);
lean_inc_ref(v_src_1019_);
lean_dec_ref(v_entry_1013_);
v___x_1020_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_1021_ = 1;
v___x_1022_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1014_, v___x_1021_);
v___x_1023_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1020_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__0));
v___x_1026_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1026_, 0, v_scope_1015_);
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__1));
v___x_1029_ = l_Lake_mkRelPathString(v_configFile_1017_);
v___x_1030_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1028_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__2));
v___x_1033_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_manifestFile_x3f_1018_);
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1032_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10));
v___x_1036_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1036_, 0, v_inherited_1016_);
v___x_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = lean_box(0);
v___x_1039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1034_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1031_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1027_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v_fields_1043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_fields_1043_, 0, v___x_1024_);
lean_ctor_set(v_fields_1043_, 1, v___x_1042_);
if (lean_obj_tag(v_src_1019_) == 0)
{
lean_object* v_dir_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1059_; 
v_dir_1044_ = lean_ctor_get(v_src_1019_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_src_1019_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1046_ = v_src_1019_;
v_isShared_1047_ = v_isSharedCheck_1059_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_dir_1044_);
lean_dec(v_src_1019_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1059_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1048_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__5));
v___x_1049_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22));
v___x_1050_ = l_Lake_mkRelPathString(v_dir_1044_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 3);
lean_ctor_set(v___x_1046_, 0, v___x_1050_);
v___x_1052_ = v___x_1046_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1049_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v___x_1038_);
v___x_1055_ = l_List_appendTR___redArg(v_fields_1043_, v___x_1054_);
v___x_1056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1048_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = l_Lean_Json_mkObj(v___x_1056_);
return v___x_1057_;
}
}
}
else
{
lean_object* v_url_1060_; lean_object* v_rev_1061_; lean_object* v_inputRev_x3f_1062_; lean_object* v_subDir_x3f_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v_url_1060_ = lean_ctor_get(v_src_1019_, 0);
lean_inc_ref(v_url_1060_);
v_rev_1061_ = lean_ctor_get(v_src_1019_, 1);
lean_inc_ref(v_rev_1061_);
v_inputRev_x3f_1062_ = lean_ctor_get(v_src_1019_, 2);
lean_inc(v_inputRev_x3f_1062_);
v_subDir_x3f_1063_ = lean_ctor_get(v_src_1019_, 3);
lean_inc(v_subDir_x3f_1063_);
lean_dec_ref(v_src_1019_);
v___x_1064_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__7));
v___x_1065_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12));
v___x_1066_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1066_, 0, v_url_1060_);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1065_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14));
v___x_1069_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1069_, 0, v_rev_1061_);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__8));
v___x_1072_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__1(v_inputRev_x3f_1062_);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__9));
v___x_1075_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_subDir_x3f_1063_);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v___x_1038_);
v___x_1078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1073_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1070_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1067_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = l_List_appendTR___redArg(v_fields_1043_, v___x_1080_);
v___x_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1064_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = l_Lean_Json_mkObj(v___x_1082_);
return v___x_1083_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0(lean_object* v_x_1087_){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0));
v___x_1089_ = lean_string_append(v___x_1088_, v_x_1087_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0___boxed(lean_object* v_x_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_x_1090_);
lean_dec_ref(v_x_1090_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f(lean_object* v_json_1112_){
_start:
{
lean_object* v_a_1114_; lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_Json_getObj_x3f(v_json_1112_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1126_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1126_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1126_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; lean_object* v___x_1124_; 
v___x_1122_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_a_1118_);
lean_dec(v_a_1118_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1122_);
v___x_1124_ = v___x_1120_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
else
{
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
v_a_1127_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1117_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1117_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
lean_ctor_set_tag(v___x_1129_, 0);
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1357_; 
v_a_1135_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1137_ = v___x_1117_;
v_isShared_1138_ = v_isSharedCheck_1357_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1117_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1357_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_1140_ = l_Lake_JsonObject_getJson_x3f(v_a_1135_, v___x_1139_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v___x_1141_; 
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v___x_1141_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__0));
v_a_1114_ = v___x_1141_;
goto v___jp_1113_;
}
else
{
lean_object* v_val_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1356_; 
v_val_1142_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1144_ = v___x_1140_;
v_isShared_1145_ = v_isSharedCheck_1356_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_val_1142_);
lean_dec(v___x_1140_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1356_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_Name_fromJson_x3f(v_val_1142_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref(v___x_1146_);
v___x_1148_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__1));
v___x_1149_ = lean_string_append(v___x_1148_, v_a_1147_);
lean_dec(v_a_1147_);
v_a_1114_ = v___x_1149_;
goto v___jp_1113_;
}
else
{
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1150_; 
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v_a_1150_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1150_);
lean_dec_ref(v___x_1146_);
v_a_1114_ = v_a_1150_;
goto v___jp_1113_;
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1355_; 
v_a_1151_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1153_ = v___x_1146_;
v_isShared_1154_ = v_isSharedCheck_1355_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1146_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1355_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v_a_1156_; lean_object* v___y_1168_; uint8_t v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v_a_1172_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; uint8_t v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v_a_1188_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; uint8_t v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v_a_1197_; lean_object* v___y_1209_; uint8_t v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v_a_1213_; lean_object* v___y_1269_; uint8_t v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1275_; uint8_t v___y_1276_; lean_object* v___y_1277_; lean_object* v_a_1278_; lean_object* v___y_1290_; uint8_t v___y_1291_; lean_object* v___y_1292_; lean_object* v_a_1295_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__0));
v___x_1332_ = l_Lake_JsonObject_getJson_x3f(v_a_1135_, v___x_1331_);
if (lean_obj_tag(v___x_1332_) == 0)
{
goto v___jp_1329_;
}
else
{
lean_object* v_val_1333_; lean_object* v___x_1334_; 
v_val_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_val_1333_);
lean_dec_ref(v___x_1332_);
v___x_1334_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(v_val_1333_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1344_; 
lean_del_object(v___x_1153_);
lean_dec(v_a_1151_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1337_ = v___x_1334_;
v_isShared_1338_ = v_isSharedCheck_1344_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1334_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1344_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1339_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__19));
v___x_1340_ = lean_string_append(v___x_1339_, v_a_1335_);
lean_dec(v_a_1335_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1340_);
v___x_1342_ = v___x_1337_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
else
{
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_del_object(v___x_1153_);
lean_dec(v_a_1151_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v_a_1345_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1334_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1334_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
lean_ctor_set_tag(v___x_1347_, 0);
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
else
{
lean_object* v_a_1353_; 
v_a_1353_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1353_);
lean_dec_ref(v___x_1334_);
if (lean_obj_tag(v_a_1353_) == 0)
{
goto v___jp_1329_;
}
else
{
lean_object* v_val_1354_; 
v_val_1354_ = lean_ctor_get(v_a_1353_, 0);
lean_inc(v_val_1354_);
lean_dec_ref(v_a_1353_);
v_a_1295_ = v_val_1354_;
goto v___jp_1294_;
}
}
}
}
v___jp_1155_:
{
lean_object* v___x_1157_; uint8_t v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1157_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__2));
v___x_1158_ = 1;
v___x_1159_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_1151_, v___x_1158_);
v___x_1160_ = lean_string_append(v___x_1157_, v___x_1159_);
lean_dec_ref(v___x_1159_);
v___x_1161_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__3));
v___x_1162_ = lean_string_append(v___x_1160_, v___x_1161_);
v___x_1163_ = lean_string_append(v___x_1162_, v_a_1156_);
lean_dec_ref(v_a_1156_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set_tag(v___x_1153_, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1163_);
v___x_1165_ = v___x_1153_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
v___jp_1167_:
{
lean_object* v___x_1174_; 
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v___y_1170_);
v___x_1174_ = v___x_1144_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___y_1170_);
v___x_1174_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1175_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1175_, 0, v_a_1151_);
lean_ctor_set(v___x_1175_, 1, v___y_1168_);
lean_ctor_set(v___x_1175_, 2, v___y_1171_);
lean_ctor_set(v___x_1175_, 3, v___x_1174_);
lean_ctor_set(v___x_1175_, 4, v_a_1172_);
lean_ctor_set_uint8(v___x_1175_, sizeof(void*)*5, v___y_1169_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1175_);
v___x_1177_ = v___x_1137_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
v___jp_1180_:
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1189_, 0, v___y_1184_);
lean_ctor_set(v___x_1189_, 1, v___y_1182_);
lean_ctor_set(v___x_1189_, 2, v___y_1181_);
lean_ctor_set(v___x_1189_, 3, v_a_1188_);
v___y_1168_ = v___y_1183_;
v___y_1169_ = v___y_1185_;
v___y_1170_ = v___y_1186_;
v___y_1171_ = v___y_1187_;
v_a_1172_ = v___x_1189_;
goto v___jp_1167_;
}
v___jp_1190_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__9));
v___x_1199_ = l_Lake_JsonObject_getJson_x3f(v_a_1135_, v___x_1198_);
lean_dec(v_a_1135_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v___x_1200_; 
lean_del_object(v___x_1153_);
v___x_1200_ = lean_box(0);
v___y_1181_ = v_a_1197_;
v___y_1182_ = v___y_1191_;
v___y_1183_ = v___y_1193_;
v___y_1184_ = v___y_1192_;
v___y_1185_ = v___y_1194_;
v___y_1186_ = v___y_1195_;
v___y_1187_ = v___y_1196_;
v_a_1188_ = v___x_1200_;
goto v___jp_1180_;
}
else
{
lean_object* v_val_1201_; lean_object* v___x_1202_; 
v_val_1201_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_val_1201_);
lean_dec_ref(v___x_1199_);
v___x_1202_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1201_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
lean_dec(v_a_1197_);
lean_dec_ref(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec_ref(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1203_);
lean_dec_ref(v___x_1202_);
v___x_1204_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__4));
v___x_1205_ = lean_string_append(v___x_1204_, v_a_1203_);
lean_dec(v_a_1203_);
v_a_1156_ = v___x_1205_;
goto v___jp_1155_;
}
else
{
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1206_; 
lean_dec(v_a_1197_);
lean_dec_ref(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec_ref(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
v_a_1206_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1206_);
lean_dec_ref(v___x_1202_);
v_a_1156_ = v_a_1206_;
goto v___jp_1155_;
}
else
{
lean_object* v_a_1207_; 
lean_del_object(v___x_1153_);
v_a_1207_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1207_);
lean_dec_ref(v___x_1202_);
v___y_1181_ = v_a_1197_;
v___y_1182_ = v___y_1191_;
v___y_1183_ = v___y_1193_;
v___y_1184_ = v___y_1192_;
v___y_1185_ = v___y_1194_;
v___y_1186_ = v___y_1195_;
v___y_1187_ = v___y_1196_;
v_a_1188_ = v_a_1207_;
goto v___jp_1180_;
}
}
}
}
v___jp_1208_:
{
lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2));
v___x_1215_ = lean_string_dec_eq(v___y_1211_, v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1216_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3));
v___x_1217_ = lean_string_dec_eq(v___y_1211_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_dec_ref(v_a_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v___y_1209_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v___x_1218_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__5));
v___x_1219_ = lean_string_append(v___x_1218_, v___y_1211_);
lean_dec_ref(v___y_1211_);
v___x_1220_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1221_ = lean_string_append(v___x_1219_, v___x_1220_);
v_a_1156_ = v___x_1221_;
goto v___jp_1155_;
}
else
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
lean_dec_ref(v___y_1211_);
v___x_1222_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12));
v___x_1223_ = l_Lake_JsonObject_getJson_x3f(v_a_1135_, v___x_1222_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v___x_1224_; 
lean_dec_ref(v_a_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v___y_1209_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v___x_1224_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__6));
v_a_1156_ = v___x_1224_;
goto v___jp_1155_;
}
else
{
lean_object* v_val_1225_; lean_object* v___x_1226_; 
v_val_1225_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_val_1225_);
lean_dec_ref(v___x_1223_);
v___x_1226_ = l_Lean_Json_getStr_x3f(v_val_1225_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_dec_ref(v_a_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v___y_1209_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1227_);
lean_dec_ref(v___x_1226_);
v___x_1228_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__7));
v___x_1229_ = lean_string_append(v___x_1228_, v_a_1227_);
lean_dec(v_a_1227_);
v_a_1156_ = v___x_1229_;
goto v___jp_1155_;
}
else
{
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1230_; 
lean_dec_ref(v_a_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v___y_1209_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v_a_1230_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1230_);
lean_dec_ref(v___x_1226_);
v_a_1156_ = v_a_1230_;
goto v___jp_1155_;
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v_a_1231_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1231_);
lean_dec_ref(v___x_1226_);
v___x_1232_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14));
v___x_1233_ = l_Lake_JsonObject_getJson_x3f(v_a_1135_, v___x_1232_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v___x_1234_; 
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v___y_1209_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v___x_1234_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__8));
v_a_1156_ = v___x_1234_;
goto v___jp_1155_;
}
else
{
lean_object* v_val_1235_; lean_object* v___x_1236_; 
v_val_1235_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_val_1235_);
lean_dec_ref(v___x_1233_);
v___x_1236_ = l_Lean_Json_getStr_x3f(v_val_1235_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v___y_1209_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref(v___x_1236_);
v___x_1238_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__9));
v___x_1239_ = lean_string_append(v___x_1238_, v_a_1237_);
lean_dec(v_a_1237_);
v_a_1156_ = v___x_1239_;
goto v___jp_1155_;
}
else
{
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1240_; 
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v___y_1209_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v_a_1240_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1240_);
lean_dec_ref(v___x_1236_);
v_a_1156_ = v_a_1240_;
goto v___jp_1155_;
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v_a_1241_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1241_);
lean_dec_ref(v___x_1236_);
v___x_1242_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__8));
v___x_1243_ = l_Lake_JsonObject_getJson_x3f(v_a_1135_, v___x_1242_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_box(0);
v___y_1191_ = v_a_1241_;
v___y_1192_ = v_a_1231_;
v___y_1193_ = v___y_1209_;
v___y_1194_ = v___y_1210_;
v___y_1195_ = v_a_1213_;
v___y_1196_ = v___y_1212_;
v_a_1197_ = v___x_1244_;
goto v___jp_1190_;
}
else
{
lean_object* v_val_1245_; lean_object* v___x_1246_; 
v_val_1245_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_val_1245_);
lean_dec_ref(v___x_1243_);
v___x_1246_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(v_val_1245_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
lean_dec(v_a_1241_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v___y_1209_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref(v___x_1246_);
v___x_1248_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__10));
v___x_1249_ = lean_string_append(v___x_1248_, v_a_1247_);
lean_dec(v_a_1247_);
v_a_1156_ = v___x_1249_;
goto v___jp_1155_;
}
else
{
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1250_; 
lean_dec(v_a_1241_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v___y_1209_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v_a_1250_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1250_);
lean_dec_ref(v___x_1246_);
v_a_1156_ = v_a_1250_;
goto v___jp_1155_;
}
else
{
lean_object* v_a_1251_; 
v_a_1251_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1251_);
lean_dec_ref(v___x_1246_);
v___y_1191_ = v_a_1241_;
v___y_1192_ = v_a_1231_;
v___y_1193_ = v___y_1209_;
v___y_1194_ = v___y_1210_;
v___y_1195_ = v_a_1213_;
v___y_1196_ = v___y_1212_;
v_a_1197_ = v_a_1251_;
goto v___jp_1190_;
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
lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_dec_ref(v___y_1211_);
v___x_1252_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22));
v___x_1253_ = l_Lake_JsonObject_getJson_x3f(v_a_1135_, v___x_1252_);
lean_dec(v_a_1135_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v___x_1254_; 
lean_dec_ref(v_a_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v___y_1209_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
v___x_1254_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__11));
v_a_1156_ = v___x_1254_;
goto v___jp_1155_;
}
else
{
lean_object* v_val_1255_; lean_object* v___x_1256_; 
v_val_1255_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_val_1255_);
lean_dec_ref(v___x_1253_);
v___x_1256_ = l_Lean_Json_getStr_x3f(v_val_1255_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
lean_dec_ref(v_a_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v___y_1209_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1257_);
lean_dec_ref(v___x_1256_);
v___x_1258_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__12));
v___x_1259_ = lean_string_append(v___x_1258_, v_a_1257_);
lean_dec(v_a_1257_);
v_a_1156_ = v___x_1259_;
goto v___jp_1155_;
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_del_object(v___x_1153_);
v_a_1260_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1256_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1256_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set_tag(v___x_1262_, 0);
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
v___y_1168_ = v___y_1209_;
v___y_1169_ = v___y_1210_;
v___y_1170_ = v_a_1213_;
v___y_1171_ = v___y_1212_;
v_a_1172_ = v___x_1265_;
goto v___jp_1167_;
}
}
}
}
}
}
v___jp_1268_:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lake_defaultManifestFile;
v___y_1209_ = v___y_1269_;
v___y_1210_ = v___y_1270_;
v___y_1211_ = v___y_1271_;
v___y_1212_ = v___y_1272_;
v_a_1213_ = v___x_1273_;
goto v___jp_1208_;
}
v___jp_1274_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__2));
v___x_1280_ = l_Lake_JsonObject_getJson_x3f(v_a_1135_, v___x_1279_);
if (lean_obj_tag(v___x_1280_) == 0)
{
v___y_1269_ = v___y_1275_;
v___y_1270_ = v___y_1276_;
v___y_1271_ = v___y_1277_;
v___y_1272_ = v_a_1278_;
goto v___jp_1268_;
}
else
{
lean_object* v_val_1281_; lean_object* v___x_1282_; 
v_val_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_val_1281_);
lean_dec_ref(v___x_1280_);
v___x_1282_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1281_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_dec_ref(v_a_1278_);
lean_dec_ref(v___y_1277_);
lean_dec_ref(v___y_1275_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref(v___x_1282_);
v___x_1284_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__13));
v___x_1285_ = lean_string_append(v___x_1284_, v_a_1283_);
lean_dec(v_a_1283_);
v_a_1156_ = v___x_1285_;
goto v___jp_1155_;
}
else
{
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1286_; 
lean_dec_ref(v_a_1278_);
lean_dec_ref(v___y_1277_);
lean_dec_ref(v___y_1275_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v_a_1286_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1286_);
lean_dec_ref(v___x_1282_);
v_a_1156_ = v_a_1286_;
goto v___jp_1155_;
}
else
{
lean_object* v_a_1287_; 
v_a_1287_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1287_);
lean_dec_ref(v___x_1282_);
if (lean_obj_tag(v_a_1287_) == 0)
{
v___y_1269_ = v___y_1275_;
v___y_1270_ = v___y_1276_;
v___y_1271_ = v___y_1277_;
v___y_1272_ = v_a_1278_;
goto v___jp_1268_;
}
else
{
lean_object* v_val_1288_; 
v_val_1288_ = lean_ctor_get(v_a_1287_, 0);
lean_inc(v_val_1288_);
lean_dec_ref(v_a_1287_);
v___y_1209_ = v___y_1275_;
v___y_1210_ = v___y_1276_;
v___y_1211_ = v___y_1277_;
v___y_1212_ = v_a_1278_;
v_a_1213_ = v_val_1288_;
goto v___jp_1208_;
}
}
}
}
}
v___jp_1289_:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lake_defaultConfigFile;
v___y_1275_ = v___y_1290_;
v___y_1276_ = v___y_1291_;
v___y_1277_ = v___y_1292_;
v_a_1278_ = v___x_1293_;
goto v___jp_1274_;
}
v___jp_1294_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__3));
v___x_1297_ = l_Lake_JsonObject_getJson_x3f(v_a_1135_, v___x_1296_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v___x_1298_; 
lean_dec_ref(v_a_1295_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v___x_1298_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__14));
v_a_1156_ = v___x_1298_;
goto v___jp_1155_;
}
else
{
lean_object* v_val_1299_; lean_object* v___x_1300_; 
v_val_1299_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_val_1299_);
lean_dec_ref(v___x_1297_);
v___x_1300_ = l_Lean_Json_getStr_x3f(v_val_1299_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
lean_dec_ref(v_a_1295_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec_ref(v___x_1300_);
v___x_1302_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__15));
v___x_1303_ = lean_string_append(v___x_1302_, v_a_1301_);
lean_dec(v_a_1301_);
v_a_1156_ = v___x_1303_;
goto v___jp_1155_;
}
else
{
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1304_; 
lean_dec_ref(v_a_1295_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v_a_1304_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1304_);
lean_dec_ref(v___x_1300_);
v_a_1156_ = v_a_1304_;
goto v___jp_1155_;
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v_a_1305_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1305_);
lean_dec_ref(v___x_1300_);
v___x_1306_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10));
v___x_1307_ = l_Lake_JsonObject_getJson_x3f(v_a_1135_, v___x_1306_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v___x_1308_; 
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1295_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v___x_1308_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__16));
v_a_1156_ = v___x_1308_;
goto v___jp_1155_;
}
else
{
lean_object* v_val_1309_; lean_object* v___x_1310_; 
v_val_1309_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_val_1309_);
lean_dec_ref(v___x_1307_);
v___x_1310_ = l_Lean_Json_getBool_x3f(v_val_1309_);
lean_dec(v_val_1309_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1295_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
lean_dec_ref(v___x_1310_);
v___x_1312_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__17));
v___x_1313_ = lean_string_append(v___x_1312_, v_a_1311_);
lean_dec(v_a_1311_);
v_a_1156_ = v___x_1313_;
goto v___jp_1155_;
}
else
{
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1314_; 
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1295_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v_a_1314_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1314_);
lean_dec_ref(v___x_1310_);
v_a_1156_ = v_a_1314_;
goto v___jp_1155_;
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v_a_1315_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1315_);
lean_dec_ref(v___x_1310_);
v___x_1316_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__1));
v___x_1317_ = l_Lake_JsonObject_getJson_x3f(v_a_1135_, v___x_1316_);
if (lean_obj_tag(v___x_1317_) == 0)
{
uint8_t v___x_1318_; 
v___x_1318_ = lean_unbox(v_a_1315_);
lean_dec(v_a_1315_);
v___y_1290_ = v_a_1295_;
v___y_1291_ = v___x_1318_;
v___y_1292_ = v_a_1305_;
goto v___jp_1289_;
}
else
{
lean_object* v_val_1319_; lean_object* v___x_1320_; 
v_val_1319_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_val_1319_);
lean_dec_ref(v___x_1317_);
v___x_1320_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1319_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_dec(v_a_1315_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1295_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_a_1321_);
lean_dec_ref(v___x_1320_);
v___x_1322_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__18));
v___x_1323_ = lean_string_append(v___x_1322_, v_a_1321_);
lean_dec(v_a_1321_);
v_a_1156_ = v___x_1323_;
goto v___jp_1155_;
}
else
{
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1324_; 
lean_dec(v_a_1315_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1295_);
lean_del_object(v___x_1144_);
lean_del_object(v___x_1137_);
lean_dec(v_a_1135_);
v_a_1324_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_a_1324_);
lean_dec_ref(v___x_1320_);
v_a_1156_ = v_a_1324_;
goto v___jp_1155_;
}
else
{
lean_object* v_a_1325_; 
v_a_1325_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_a_1325_);
lean_dec_ref(v___x_1320_);
if (lean_obj_tag(v_a_1325_) == 0)
{
uint8_t v___x_1326_; 
v___x_1326_ = lean_unbox(v_a_1315_);
lean_dec(v_a_1315_);
v___y_1290_ = v_a_1295_;
v___y_1291_ = v___x_1326_;
v___y_1292_ = v_a_1305_;
goto v___jp_1289_;
}
else
{
lean_object* v_val_1327_; uint8_t v___x_1328_; 
v_val_1327_ = lean_ctor_get(v_a_1325_, 0);
lean_inc(v_val_1327_);
lean_dec_ref(v_a_1325_);
v___x_1328_ = lean_unbox(v_a_1315_);
lean_dec(v_a_1315_);
v___y_1275_ = v_a_1295_;
v___y_1276_ = v___x_1328_;
v___y_1277_ = v_a_1305_;
v_a_1278_ = v_val_1327_;
goto v___jp_1274_;
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
v___jp_1329_:
{
lean_object* v___x_1330_; 
v___x_1330_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v_a_1295_ = v___x_1330_;
goto v___jp_1294_;
}
}
}
}
}
}
}
}
}
v___jp_1113_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_a_1114_);
lean_dec_ref(v_a_1114_);
v___x_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
return v___x_1116_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setInherited(lean_object* v_entry_1360_){
_start:
{
lean_object* v_name_1361_; lean_object* v_scope_1362_; lean_object* v_configFile_1363_; lean_object* v_manifestFile_x3f_1364_; lean_object* v_src_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1373_; 
v_name_1361_ = lean_ctor_get(v_entry_1360_, 0);
v_scope_1362_ = lean_ctor_get(v_entry_1360_, 1);
v_configFile_1363_ = lean_ctor_get(v_entry_1360_, 2);
v_manifestFile_x3f_1364_ = lean_ctor_get(v_entry_1360_, 3);
v_src_1365_ = lean_ctor_get(v_entry_1360_, 4);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_entry_1360_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1367_ = v_entry_1360_;
v_isShared_1368_ = v_isSharedCheck_1373_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_src_1365_);
lean_inc(v_manifestFile_x3f_1364_);
lean_inc(v_configFile_1363_);
lean_inc(v_scope_1362_);
lean_inc(v_name_1361_);
lean_dec(v_entry_1360_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1373_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
uint8_t v___x_1369_; lean_object* v___x_1371_; 
v___x_1369_ = 1;
if (v_isShared_1368_ == 0)
{
v___x_1371_ = v___x_1367_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_name_1361_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_scope_1362_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v_configFile_1363_);
lean_ctor_set(v_reuseFailAlloc_1372_, 3, v_manifestFile_x3f_1364_);
lean_ctor_set(v_reuseFailAlloc_1372_, 4, v_src_1365_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_ctor_set_uint8(v___x_1371_, sizeof(void*)*5, v___x_1369_);
return v___x_1371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setConfigFile(lean_object* v_path_1374_, lean_object* v_entry_1375_){
_start:
{
lean_object* v_name_1376_; lean_object* v_scope_1377_; uint8_t v_inherited_1378_; lean_object* v_manifestFile_x3f_1379_; lean_object* v_src_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
v_name_1376_ = lean_ctor_get(v_entry_1375_, 0);
v_scope_1377_ = lean_ctor_get(v_entry_1375_, 1);
v_inherited_1378_ = lean_ctor_get_uint8(v_entry_1375_, sizeof(void*)*5);
v_manifestFile_x3f_1379_ = lean_ctor_get(v_entry_1375_, 3);
v_src_1380_ = lean_ctor_get(v_entry_1375_, 4);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_entry_1375_);
if (v_isSharedCheck_1387_ == 0)
{
lean_object* v_unused_1388_; 
v_unused_1388_ = lean_ctor_get(v_entry_1375_, 2);
lean_dec(v_unused_1388_);
v___x_1382_ = v_entry_1375_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_src_1380_);
lean_inc(v_manifestFile_x3f_1379_);
lean_inc(v_scope_1377_);
lean_inc(v_name_1376_);
lean_dec(v_entry_1375_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 2, v_path_1374_);
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_name_1376_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_scope_1377_);
lean_ctor_set(v_reuseFailAlloc_1386_, 2, v_path_1374_);
lean_ctor_set(v_reuseFailAlloc_1386_, 3, v_manifestFile_x3f_1379_);
lean_ctor_set(v_reuseFailAlloc_1386_, 4, v_src_1380_);
lean_ctor_set_uint8(v_reuseFailAlloc_1386_, sizeof(void*)*5, v_inherited_1378_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setManifestFile(lean_object* v_path_x3f_1389_, lean_object* v_entry_1390_){
_start:
{
lean_object* v_name_1391_; lean_object* v_scope_1392_; uint8_t v_inherited_1393_; lean_object* v_configFile_1394_; lean_object* v_src_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
v_name_1391_ = lean_ctor_get(v_entry_1390_, 0);
v_scope_1392_ = lean_ctor_get(v_entry_1390_, 1);
v_inherited_1393_ = lean_ctor_get_uint8(v_entry_1390_, sizeof(void*)*5);
v_configFile_1394_ = lean_ctor_get(v_entry_1390_, 2);
v_src_1395_ = lean_ctor_get(v_entry_1390_, 4);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_entry_1390_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; 
v_unused_1403_ = lean_ctor_get(v_entry_1390_, 3);
lean_dec(v_unused_1403_);
v___x_1397_ = v_entry_1390_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_src_1395_);
lean_inc(v_configFile_1394_);
lean_inc(v_scope_1392_);
lean_inc(v_name_1391_);
lean_dec(v_entry_1390_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 3, v_path_x3f_1389_);
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_name_1391_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_scope_1392_);
lean_ctor_set(v_reuseFailAlloc_1401_, 2, v_configFile_1394_);
lean_ctor_set(v_reuseFailAlloc_1401_, 3, v_path_x3f_1389_);
lean_ctor_set(v_reuseFailAlloc_1401_, 4, v_src_1395_);
lean_ctor_set_uint8(v_reuseFailAlloc_1401_, sizeof(void*)*5, v_inherited_1393_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_inDirectory(lean_object* v_pkgDir_1404_, lean_object* v_entry_1405_){
_start:
{
lean_object* v_src_1406_; 
v_src_1406_ = lean_ctor_get(v_entry_1405_, 4);
lean_inc_ref(v_src_1406_);
if (lean_obj_tag(v_src_1406_) == 0)
{
lean_object* v_name_1407_; lean_object* v_scope_1408_; uint8_t v_inherited_1409_; lean_object* v_configFile_1410_; lean_object* v_manifestFile_x3f_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1427_; 
v_name_1407_ = lean_ctor_get(v_entry_1405_, 0);
v_scope_1408_ = lean_ctor_get(v_entry_1405_, 1);
v_inherited_1409_ = lean_ctor_get_uint8(v_entry_1405_, sizeof(void*)*5);
v_configFile_1410_ = lean_ctor_get(v_entry_1405_, 2);
v_manifestFile_x3f_1411_ = lean_ctor_get(v_entry_1405_, 3);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_entry_1405_);
if (v_isSharedCheck_1427_ == 0)
{
lean_object* v_unused_1428_; 
v_unused_1428_ = lean_ctor_get(v_entry_1405_, 4);
lean_dec(v_unused_1428_);
v___x_1413_ = v_entry_1405_;
v_isShared_1414_ = v_isSharedCheck_1427_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_manifestFile_x3f_1411_);
lean_inc(v_configFile_1410_);
lean_inc(v_scope_1408_);
lean_inc(v_name_1407_);
lean_dec(v_entry_1405_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1427_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v_dir_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1426_; 
v_dir_1415_ = lean_ctor_get(v_src_1406_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_src_1406_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1417_ = v_src_1406_;
v_isShared_1418_ = v_isSharedCheck_1426_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_dir_1415_);
lean_dec(v_src_1406_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1426_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1419_ = l_Lake_joinRelative(v_pkgDir_1404_, v_dir_1415_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1419_);
v___x_1421_ = v___x_1417_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1423_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 4, v___x_1421_);
v___x_1423_ = v___x_1413_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_name_1407_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_scope_1408_);
lean_ctor_set(v_reuseFailAlloc_1424_, 2, v_configFile_1410_);
lean_ctor_set(v_reuseFailAlloc_1424_, 3, v_manifestFile_x3f_1411_);
lean_ctor_set(v_reuseFailAlloc_1424_, 4, v___x_1421_);
lean_ctor_set_uint8(v_reuseFailAlloc_1424_, sizeof(void*)*5, v_inherited_1409_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
else
{
lean_dec_ref(v_src_1406_);
lean_dec_ref(v_pkgDir_1404_);
return v_entry_1405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(lean_object* v_x_1429_){
_start:
{
if (lean_obj_tag(v_x_1429_) == 0)
{
lean_object* v_name_1430_; uint8_t v_inherited_1431_; lean_object* v_dir_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v_name_1430_ = lean_ctor_get(v_x_1429_, 0);
v_inherited_1431_ = lean_ctor_get_uint8(v_x_1429_, sizeof(void*)*3);
v_dir_1432_ = lean_ctor_get(v_x_1429_, 2);
v___x_1433_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_1434_ = l_Lake_defaultConfigFile;
v___x_1435_ = lean_box(0);
lean_inc_ref(v_dir_1432_);
v___x_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1436_, 0, v_dir_1432_);
lean_inc(v_name_1430_);
v___x_1437_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1437_, 0, v_name_1430_);
lean_ctor_set(v___x_1437_, 1, v___x_1433_);
lean_ctor_set(v___x_1437_, 2, v___x_1434_);
lean_ctor_set(v___x_1437_, 3, v___x_1435_);
lean_ctor_set(v___x_1437_, 4, v___x_1436_);
lean_ctor_set_uint8(v___x_1437_, sizeof(void*)*5, v_inherited_1431_);
return v___x_1437_;
}
else
{
lean_object* v_name_1438_; uint8_t v_inherited_1439_; lean_object* v_url_1440_; lean_object* v_rev_1441_; lean_object* v_inputRev_x3f_1442_; lean_object* v_subDir_x3f_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v_name_1438_ = lean_ctor_get(v_x_1429_, 0);
v_inherited_1439_ = lean_ctor_get_uint8(v_x_1429_, sizeof(void*)*6);
v_url_1440_ = lean_ctor_get(v_x_1429_, 2);
v_rev_1441_ = lean_ctor_get(v_x_1429_, 3);
v_inputRev_x3f_1442_ = lean_ctor_get(v_x_1429_, 4);
v_subDir_x3f_1443_ = lean_ctor_get(v_x_1429_, 5);
v___x_1444_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_1445_ = l_Lake_defaultConfigFile;
v___x_1446_ = lean_box(0);
lean_inc(v_subDir_x3f_1443_);
lean_inc(v_inputRev_x3f_1442_);
lean_inc_ref(v_rev_1441_);
lean_inc_ref(v_url_1440_);
v___x_1447_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1447_, 0, v_url_1440_);
lean_ctor_set(v___x_1447_, 1, v_rev_1441_);
lean_ctor_set(v___x_1447_, 2, v_inputRev_x3f_1442_);
lean_ctor_set(v___x_1447_, 3, v_subDir_x3f_1443_);
lean_inc(v_name_1438_);
v___x_1448_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1448_, 0, v_name_1438_);
lean_ctor_set(v___x_1448_, 1, v___x_1444_);
lean_ctor_set(v___x_1448_, 2, v___x_1445_);
lean_ctor_set(v___x_1448_, 3, v___x_1446_);
lean_ctor_set(v___x_1448_, 4, v___x_1447_);
lean_ctor_set_uint8(v___x_1448_, sizeof(void*)*5, v_inherited_1439_);
return v___x_1448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6___boxed(lean_object* v_x_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(v_x_1449_);
lean_dec_ref(v_x_1449_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_addPackage(lean_object* v_entry_1451_, lean_object* v_self_1452_){
_start:
{
lean_object* v_name_1453_; lean_object* v_lakeDir_1454_; lean_object* v_packagesDir_x3f_1455_; lean_object* v_packages_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1464_; 
v_name_1453_ = lean_ctor_get(v_self_1452_, 0);
v_lakeDir_1454_ = lean_ctor_get(v_self_1452_, 1);
v_packagesDir_x3f_1455_ = lean_ctor_get(v_self_1452_, 2);
v_packages_1456_ = lean_ctor_get(v_self_1452_, 3);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_self_1452_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1458_ = v_self_1452_;
v_isShared_1459_ = v_isSharedCheck_1464_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_packages_1456_);
lean_inc(v_packagesDir_x3f_1455_);
lean_inc(v_lakeDir_1454_);
lean_inc(v_name_1453_);
lean_dec(v_self_1452_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1464_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1460_ = lean_array_push(v_packages_1456_, v_entry_1451_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 3, v___x_1460_);
v___x_1462_ = v___x_1458_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_name_1453_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_lakeDir_1454_);
lean_ctor_set(v_reuseFailAlloc_1463_, 2, v_packagesDir_x3f_1455_);
lean_ctor_set(v_reuseFailAlloc_1463_, 3, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(size_t v_sz_1465_, size_t v_i_1466_, lean_object* v_bs_1467_){
_start:
{
uint8_t v___x_1468_; 
v___x_1468_ = lean_usize_dec_lt(v_i_1466_, v_sz_1465_);
if (v___x_1468_ == 0)
{
return v_bs_1467_;
}
else
{
lean_object* v_v_1469_; lean_object* v___x_1470_; lean_object* v_bs_x27_1471_; lean_object* v___x_1472_; size_t v___x_1473_; size_t v___x_1474_; lean_object* v___x_1475_; 
v_v_1469_ = lean_array_uget(v_bs_1467_, v_i_1466_);
v___x_1470_ = lean_unsigned_to_nat(0u);
v_bs_x27_1471_ = lean_array_uset(v_bs_1467_, v_i_1466_, v___x_1470_);
v___x_1472_ = l_Lake_PackageEntry_toJson(v_v_1469_);
v___x_1473_ = ((size_t)1ULL);
v___x_1474_ = lean_usize_add(v_i_1466_, v___x_1473_);
v___x_1475_ = lean_array_uset(v_bs_x27_1471_, v_i_1466_, v___x_1472_);
v_i_1466_ = v___x_1474_;
v_bs_1467_ = v___x_1475_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1477_, lean_object* v_i_1478_, lean_object* v_bs_1479_){
_start:
{
size_t v_sz_boxed_1480_; size_t v_i_boxed_1481_; lean_object* v_res_1482_; 
v_sz_boxed_1480_ = lean_unbox_usize(v_sz_1477_);
lean_dec(v_sz_1477_);
v_i_boxed_1481_ = lean_unbox_usize(v_i_1478_);
lean_dec(v_i_1478_);
v_res_1482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(v_sz_boxed_1480_, v_i_boxed_1481_, v_bs_1479_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_Manifest_toJson_spec__0(lean_object* v_a_1483_){
_start:
{
size_t v_sz_1484_; size_t v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v_sz_1484_ = lean_array_size(v_a_1483_);
v___x_1485_ = ((size_t)0ULL);
v___x_1486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(v_sz_1484_, v___x_1485_, v_a_1483_);
v___x_1487_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
return v___x_1487_;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__1(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = ((lean_object*)(l_Lake_Manifest_version___closed__2));
v___x_1490_ = l_Lake_StdVer_toString(v___x_1489_);
return v___x_1490_;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__2(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__1, &l_Lake_Manifest_toJson___closed__1_once, _init_l_Lake_Manifest_toJson___closed__1);
v___x_1492_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
return v___x_1492_;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__3(void){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1493_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__2, &l_Lake_Manifest_toJson___closed__2_once, _init_l_Lake_Manifest_toJson___closed__2);
v___x_1494_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__0));
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_ctor_set(v___x_1495_, 1, v___x_1493_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_toJson(lean_object* v_self_1499_){
_start:
{
lean_object* v_name_1500_; lean_object* v_lakeDir_1501_; lean_object* v_packagesDir_x3f_1502_; lean_object* v_packages_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_name_1500_ = lean_ctor_get(v_self_1499_, 0);
lean_inc(v_name_1500_);
v_lakeDir_1501_ = lean_ctor_get(v_self_1499_, 1);
lean_inc_ref(v_lakeDir_1501_);
v_packagesDir_x3f_1502_ = lean_ctor_get(v_self_1499_, 2);
lean_inc(v_packagesDir_x3f_1502_);
v_packages_1503_ = lean_ctor_get(v_self_1499_, 3);
lean_inc_ref(v_packages_1503_);
lean_dec_ref(v_self_1499_);
v___x_1504_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__3, &l_Lake_Manifest_toJson___closed__3_once, _init_l_Lake_Manifest_toJson___closed__3);
v___x_1505_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_1506_ = 1;
v___x_1507_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1500_, v___x_1506_);
v___x_1508_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
v___x_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1505_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__4));
v___x_1511_ = l_Lake_mkRelPathString(v_lakeDir_1501_);
v___x_1512_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
v___x_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1510_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
v___x_1514_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__5));
v___x_1515_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_packagesDir_x3f_1502_);
v___x_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1514_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
v___x_1517_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__6));
v___x_1518_ = l_Array_toJson___at___00Lake_Manifest_toJson_spec__0(v_packages_1503_);
v___x_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = lean_box(0);
v___x_1521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1519_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
v___x_1522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1516_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
v___x_1523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1513_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___x_1524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1509_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
v___x_1525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1504_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___x_1526_ = l_Lean_Json_mkObj(v___x_1525_);
return v___x_1526_;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6(void){
_start:
{
lean_object* v_natZero_1537_; lean_object* v_intZero_1538_; 
v_natZero_1537_ = lean_unsigned_to_nat(0u);
v_intZero_1538_ = lean_nat_to_int(v_natZero_1537_);
return v_intZero_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(lean_object* v_obj_1544_){
_start:
{
lean_object* v___y_1546_; lean_object* v_ver_1554_; lean_object* v_major_1555_; lean_object* v_ver_1572_; lean_object* v_a_1581_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__0));
v___x_1608_ = l_Lake_JsonObject_getJson_x3f(v_obj_1544_, v___x_1607_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8));
v___x_1610_ = l_Lake_JsonObject_getJson_x3f(v_obj_1544_, v___x_1609_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v___x_1611_; 
v___x_1611_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__10));
return v___x_1611_;
}
else
{
lean_object* v_val_1612_; 
v_val_1612_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_val_1612_);
lean_dec_ref(v___x_1610_);
v_a_1581_ = v_val_1612_;
goto v___jp_1580_;
}
}
else
{
lean_object* v_val_1613_; 
v_val_1613_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_val_1613_);
lean_dec_ref(v___x_1608_);
v_a_1581_ = v_val_1613_;
goto v___jp_1580_;
}
v___jp_1545_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1547_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__0));
v___x_1548_ = l_Lake_SemVerCore_toString(v___y_1546_);
v___x_1549_ = lean_string_append(v___x_1547_, v___x_1548_);
lean_dec_ref(v___x_1548_);
v___x_1550_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1551_ = lean_string_append(v___x_1549_, v___x_1550_);
v___x_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
return v___x_1552_;
}
v___jp_1553_:
{
lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1556_ = lean_unsigned_to_nat(1u);
v___x_1557_ = lean_nat_dec_lt(v___x_1556_, v_major_1555_);
lean_dec(v_major_1555_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; uint8_t v___x_1559_; 
v___x_1558_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__1));
v___x_1559_ = l_Lake_instOrdSemVerCore_ord(v_ver_1554_, v___x_1558_);
if (v___x_1559_ == 0)
{
v___y_1546_ = v_ver_1554_;
goto v___jp_1545_;
}
else
{
if (v___x_1557_ == 0)
{
lean_object* v___x_1560_; 
v___x_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1560_, 0, v_ver_1554_);
return v___x_1560_;
}
else
{
v___y_1546_ = v_ver_1554_;
goto v___jp_1545_;
}
}
}
else
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1561_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__2));
v___x_1562_ = l_Lake_SemVerCore_toString(v_ver_1554_);
v___x_1563_ = lean_string_append(v___x_1561_, v___x_1562_);
lean_dec_ref(v___x_1562_);
v___x_1564_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__3));
v___x_1565_ = lean_string_append(v___x_1563_, v___x_1564_);
v___x_1566_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__1, &l_Lake_Manifest_toJson___closed__1_once, _init_l_Lake_Manifest_toJson___closed__1);
v___x_1567_ = lean_string_append(v___x_1565_, v___x_1566_);
v___x_1568_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4));
v___x_1569_ = lean_string_append(v___x_1567_, v___x_1568_);
v___x_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
return v___x_1570_;
}
}
v___jp_1571_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1573_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__5));
v___x_1574_ = lean_unsigned_to_nat(80u);
v___x_1575_ = l_Lean_Json_pretty(v_ver_1572_, v___x_1574_);
v___x_1576_ = lean_string_append(v___x_1573_, v___x_1575_);
lean_dec_ref(v___x_1575_);
v___x_1577_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4));
v___x_1578_ = lean_string_append(v___x_1576_, v___x_1577_);
v___x_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
return v___x_1579_;
}
v___jp_1580_:
{
switch(lean_obj_tag(v_a_1581_))
{
case 2:
{
lean_object* v_n_1582_; lean_object* v_mantissa_1583_; lean_object* v_exponent_1584_; lean_object* v_natZero_1585_; lean_object* v_intZero_1586_; uint8_t v_isNeg_1587_; 
v_n_1582_ = lean_ctor_get(v_a_1581_, 0);
v_mantissa_1583_ = lean_ctor_get(v_n_1582_, 0);
v_exponent_1584_ = lean_ctor_get(v_n_1582_, 1);
v_natZero_1585_ = lean_unsigned_to_nat(0u);
v_intZero_1586_ = lean_obj_once(&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6, &l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6_once, _init_l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6);
v_isNeg_1587_ = lean_int_dec_lt(v_mantissa_1583_, v_intZero_1586_);
if (v_isNeg_1587_ == 0)
{
uint8_t v___x_1588_; 
v___x_1588_ = lean_nat_dec_eq(v_exponent_1584_, v_natZero_1585_);
if (v___x_1588_ == 0)
{
v_ver_1572_ = v_a_1581_;
goto v___jp_1571_;
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1590_; 
lean_inc(v_mantissa_1583_);
lean_dec_ref(v_a_1581_);
v_a_1589_ = lean_nat_abs(v_mantissa_1583_);
lean_dec(v_mantissa_1583_);
v___x_1590_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1590_, 0, v_natZero_1585_);
lean_ctor_set(v___x_1590_, 1, v_a_1589_);
lean_ctor_set(v___x_1590_, 2, v_natZero_1585_);
v_ver_1554_ = v___x_1590_;
v_major_1555_ = v_natZero_1585_;
goto v___jp_1553_;
}
}
else
{
v_ver_1572_ = v_a_1581_;
goto v___jp_1571_;
}
}
case 3:
{
lean_object* v_s_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v_s_1591_ = lean_ctor_get(v_a_1581_, 0);
lean_inc_ref(v_s_1591_);
lean_dec_ref(v_a_1581_);
v___x_1592_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7));
v___x_1593_ = lean_unsigned_to_nat(0u);
v___x_1594_ = lean_string_utf8_byte_size(v_s_1591_);
v___x_1595_ = l___private_Lake_Util_Version_0__Lake_runVerParse(lean_box(0), v_s_1591_, v___x_1592_, v___x_1593_, v___x_1594_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v_toSemVerCore_1605_; lean_object* v_major_1606_; 
v_a_1604_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1604_);
lean_dec_ref(v___x_1595_);
v_toSemVerCore_1605_ = lean_ctor_get(v_a_1604_, 0);
lean_inc_ref(v_toSemVerCore_1605_);
lean_dec(v_a_1604_);
v_major_1606_ = lean_ctor_get(v_toSemVerCore_1605_, 0);
lean_inc(v_major_1606_);
v_ver_1554_ = v_toSemVerCore_1605_;
v_major_1555_ = v_major_1606_;
goto v___jp_1553_;
}
}
default: 
{
v_ver_1572_ = v_a_1581_;
goto v___jp_1571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___boxed(lean_object* v_obj_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_obj_1614_);
lean_dec(v_obj_1614_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(size_t v_sz_1616_, size_t v_i_1617_, lean_object* v_bs_1618_){
_start:
{
uint8_t v___x_1619_; 
v___x_1619_ = lean_usize_dec_lt(v_i_1617_, v_sz_1616_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; 
v___x_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1620_, 0, v_bs_1618_);
return v___x_1620_;
}
else
{
lean_object* v_v_1621_; lean_object* v___x_1622_; 
v_v_1621_ = lean_array_uget_borrowed(v_bs_1618_, v_i_1617_);
lean_inc(v_v_1621_);
v___x_1622_ = l_Lake_PackageEntry_fromJson_x3f(v_v_1621_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec_ref(v_bs_1618_);
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1632_; lean_object* v_bs_x27_1633_; size_t v___x_1634_; size_t v___x_1635_; lean_object* v___x_1636_; 
v_a_1631_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1631_);
lean_dec_ref(v___x_1622_);
v___x_1632_ = lean_unsigned_to_nat(0u);
v_bs_x27_1633_ = lean_array_uset(v_bs_1618_, v_i_1617_, v___x_1632_);
v___x_1634_ = ((size_t)1ULL);
v___x_1635_ = lean_usize_add(v_i_1617_, v___x_1634_);
v___x_1636_ = lean_array_uset(v_bs_x27_1633_, v_i_1617_, v_a_1631_);
v_i_1617_ = v___x_1635_;
v_bs_1618_ = v___x_1636_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_1638_, lean_object* v_i_1639_, lean_object* v_bs_1640_){
_start:
{
size_t v_sz_boxed_1641_; size_t v_i_boxed_1642_; lean_object* v_res_1643_; 
v_sz_boxed_1641_ = lean_unbox_usize(v_sz_1638_);
lean_dec(v_sz_1638_);
v_i_boxed_1642_ = lean_unbox_usize(v_i_1639_);
lean_dec(v_i_1639_);
v_res_1643_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(v_sz_boxed_1641_, v_i_boxed_1642_, v_bs_1640_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1(lean_object* v_x_1645_){
_start:
{
if (lean_obj_tag(v_x_1645_) == 4)
{
lean_object* v_elems_1646_; size_t v_sz_1647_; size_t v___x_1648_; lean_object* v___x_1649_; 
v_elems_1646_ = lean_ctor_get(v_x_1645_, 0);
lean_inc_ref(v_elems_1646_);
lean_dec_ref(v_x_1645_);
v_sz_1647_ = lean_array_size(v_elems_1646_);
v___x_1648_ = ((size_t)0ULL);
v___x_1649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(v_sz_1647_, v___x_1648_, v_elems_1646_);
return v___x_1649_;
}
else
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1650_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1___closed__0));
v___x_1651_ = lean_unsigned_to_nat(80u);
v___x_1652_ = l_Lean_Json_pretty(v_x_1645_, v___x_1651_);
v___x_1653_ = lean_string_append(v___x_1650_, v___x_1652_);
lean_dec_ref(v___x_1652_);
v___x_1654_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1655_ = lean_string_append(v___x_1653_, v___x_1654_);
v___x_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
return v___x_1656_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1(lean_object* v_x_1659_){
_start:
{
if (lean_obj_tag(v_x_1659_) == 0)
{
lean_object* v___x_1660_; 
v___x_1660_ = ((lean_object*)(l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1___closed__0));
return v___x_1660_;
}
else
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1(v_x_1659_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1678_; 
v_a_1670_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1672_ = v___x_1661_;
v_isShared_1673_ = v_isSharedCheck_1678_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1661_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1678_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; lean_object* v___x_1676_; 
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_a_1670_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1674_);
v___x_1676_ = v___x_1672_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(size_t v_sz_1679_, size_t v_i_1680_, lean_object* v_bs_1681_){
_start:
{
uint8_t v___x_1682_; 
v___x_1682_ = lean_usize_dec_lt(v_i_1680_, v_sz_1679_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1683_, 0, v_bs_1681_);
return v___x_1683_;
}
else
{
lean_object* v_v_1684_; lean_object* v___x_1685_; 
v_v_1684_ = lean_array_uget_borrowed(v_bs_1681_, v_i_1680_);
lean_inc(v_v_1684_);
v___x_1685_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson(v_v_1684_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec_ref(v_bs_1681_);
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1685_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1685_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1695_; lean_object* v_bs_x27_1696_; size_t v___x_1697_; size_t v___x_1698_; lean_object* v___x_1699_; 
v_a_1694_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_a_1694_);
lean_dec_ref(v___x_1685_);
v___x_1695_ = lean_unsigned_to_nat(0u);
v_bs_x27_1696_ = lean_array_uset(v_bs_1681_, v_i_1680_, v___x_1695_);
v___x_1697_ = ((size_t)1ULL);
v___x_1698_ = lean_usize_add(v_i_1680_, v___x_1697_);
v___x_1699_ = lean_array_uset(v_bs_x27_1696_, v_i_1680_, v_a_1694_);
v_i_1680_ = v___x_1698_;
v_bs_1681_ = v___x_1699_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_1701_, lean_object* v_i_1702_, lean_object* v_bs_1703_){
_start:
{
size_t v_sz_boxed_1704_; size_t v_i_boxed_1705_; lean_object* v_res_1706_; 
v_sz_boxed_1704_ = lean_unbox_usize(v_sz_1701_);
lean_dec(v_sz_1701_);
v_i_boxed_1705_ = lean_unbox_usize(v_i_1702_);
lean_dec(v_i_1702_);
v_res_1706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(v_sz_boxed_1704_, v_i_boxed_1705_, v_bs_1703_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3(lean_object* v_x_1707_){
_start:
{
if (lean_obj_tag(v_x_1707_) == 4)
{
lean_object* v_elems_1708_; size_t v_sz_1709_; size_t v___x_1710_; lean_object* v___x_1711_; 
v_elems_1708_ = lean_ctor_get(v_x_1707_, 0);
lean_inc_ref(v_elems_1708_);
lean_dec_ref(v_x_1707_);
v_sz_1709_ = lean_array_size(v_elems_1708_);
v___x_1710_ = ((size_t)0ULL);
v___x_1711_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(v_sz_1709_, v___x_1710_, v_elems_1708_);
return v___x_1711_;
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1712_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1___closed__0));
v___x_1713_ = lean_unsigned_to_nat(80u);
v___x_1714_ = l_Lean_Json_pretty(v_x_1707_, v___x_1713_);
v___x_1715_ = lean_string_append(v___x_1712_, v___x_1714_);
lean_dec_ref(v___x_1714_);
v___x_1716_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1717_ = lean_string_append(v___x_1715_, v___x_1716_);
v___x_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
return v___x_1718_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2(lean_object* v_x_1721_){
_start:
{
if (lean_obj_tag(v_x_1721_) == 0)
{
lean_object* v___x_1722_; 
v___x_1722_ = ((lean_object*)(l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2___closed__0));
return v___x_1722_;
}
else
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3(v_x_1721_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1723_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1723_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
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
v_a_1732_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1734_ = v___x_1723_;
v_isShared_1735_ = v_isSharedCheck_1740_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1723_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1740_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1736_, 0, v_a_1732_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(size_t v_sz_1741_, size_t v_i_1742_, lean_object* v_bs_1743_){
_start:
{
uint8_t v___x_1744_; 
v___x_1744_ = lean_usize_dec_lt(v_i_1742_, v_sz_1741_);
if (v___x_1744_ == 0)
{
return v_bs_1743_;
}
else
{
lean_object* v_v_1745_; lean_object* v___x_1746_; lean_object* v_bs_x27_1747_; lean_object* v___x_1748_; size_t v___x_1749_; size_t v___x_1750_; lean_object* v___x_1751_; 
v_v_1745_ = lean_array_uget(v_bs_1743_, v_i_1742_);
v___x_1746_ = lean_unsigned_to_nat(0u);
v_bs_x27_1747_ = lean_array_uset(v_bs_1743_, v_i_1742_, v___x_1746_);
v___x_1748_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(v_v_1745_);
lean_dec(v_v_1745_);
v___x_1749_ = ((size_t)1ULL);
v___x_1750_ = lean_usize_add(v_i_1742_, v___x_1749_);
v___x_1751_ = lean_array_uset(v_bs_x27_1747_, v_i_1742_, v___x_1748_);
v_i_1742_ = v___x_1750_;
v_bs_1743_ = v___x_1751_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0___boxed(lean_object* v_sz_1753_, lean_object* v_i_1754_, lean_object* v_bs_1755_){
_start:
{
size_t v_sz_boxed_1756_; size_t v_i_boxed_1757_; lean_object* v_res_1758_; 
v_sz_boxed_1756_ = lean_unbox_usize(v_sz_1753_);
lean_dec(v_sz_1753_);
v_i_boxed_1757_ = lean_unbox_usize(v_i_1754_);
lean_dec(v_i_1754_);
v_res_1758_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(v_sz_boxed_1756_, v_i_boxed_1757_, v_bs_1755_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(lean_object* v_ver_1772_, lean_object* v_obj_1773_){
_start:
{
lean_object* v_a_1775_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1784_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__4));
v___x_1785_ = l_Lake_StdVer_compare(v_ver_1772_, v___x_1784_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__6));
v___x_1787_ = l_Lake_JsonObject_getJson_x3f(v_obj_1773_, v___x_1786_);
if (lean_obj_tag(v___x_1787_) == 0)
{
goto v___jp_1780_;
}
else
{
lean_object* v_val_1788_; lean_object* v___x_1789_; 
v_val_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_val_1788_);
lean_dec_ref(v___x_1787_);
v___x_1789_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2(v_val_1788_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1799_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1792_ = v___x_1789_;
v_isShared_1793_ = v_isSharedCheck_1799_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1799_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1797_; 
v___x_1794_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5));
v___x_1795_ = lean_string_append(v___x_1794_, v_a_1790_);
lean_dec(v_a_1790_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v___x_1795_);
v___x_1797_ = v___x_1792_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
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
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
v_a_1800_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1789_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1789_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
lean_ctor_set_tag(v___x_1802_, 0);
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
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
lean_object* v_a_1808_; 
v_a_1808_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1808_);
lean_dec_ref(v___x_1789_);
if (lean_obj_tag(v_a_1808_) == 0)
{
goto v___jp_1780_;
}
else
{
lean_object* v_val_1809_; 
v_val_1809_ = lean_ctor_get(v_a_1808_, 0);
lean_inc(v_val_1809_);
lean_dec_ref(v_a_1808_);
v_a_1775_ = v_val_1809_;
goto v___jp_1774_;
}
}
}
}
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__6));
v___x_1811_ = l_Lake_JsonObject_getJson_x3f(v_obj_1773_, v___x_1810_);
if (lean_obj_tag(v___x_1811_) == 0)
{
goto v___jp_1782_;
}
else
{
lean_object* v_val_1812_; lean_object* v___x_1813_; 
v_val_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_val_1812_);
lean_dec_ref(v___x_1811_);
v___x_1813_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1(v_val_1812_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1823_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1823_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1823_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1818_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5));
v___x_1819_ = lean_string_append(v___x_1818_, v_a_1814_);
lean_dec(v_a_1814_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1819_);
v___x_1821_ = v___x_1816_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
else
{
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
v_a_1824_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1813_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1813_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set_tag(v___x_1826_, 0);
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
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
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1840_; 
v_a_1832_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1834_ = v___x_1813_;
v_isShared_1835_ = v_isSharedCheck_1840_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1813_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1840_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
if (lean_obj_tag(v_a_1832_) == 0)
{
lean_del_object(v___x_1834_);
goto v___jp_1782_;
}
else
{
lean_object* v_val_1836_; lean_object* v___x_1838_; 
v_val_1836_ = lean_ctor_get(v_a_1832_, 0);
lean_inc(v_val_1836_);
lean_dec_ref(v_a_1832_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v_val_1836_);
v___x_1838_ = v___x_1834_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_val_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
}
}
}
v___jp_1774_:
{
size_t v_sz_1776_; size_t v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v_sz_1776_ = lean_array_size(v_a_1775_);
v___x_1777_ = ((size_t)0ULL);
v___x_1778_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(v_sz_1776_, v___x_1777_, v_a_1775_);
v___x_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
return v___x_1779_;
}
v___jp_1780_:
{
lean_object* v___x_1781_; 
v___x_1781_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__0));
v_a_1775_ = v___x_1781_;
goto v___jp_1774_;
}
v___jp_1782_:
{
lean_object* v___x_1783_; 
v___x_1783_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__2));
return v___x_1783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___boxed(lean_object* v_ver_1841_, lean_object* v_obj_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(v_ver_1841_, v_obj_1842_);
lean_dec(v_obj_1842_);
lean_dec_ref(v_ver_1841_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0(lean_object* v_x_1846_){
_start:
{
if (lean_obj_tag(v_x_1846_) == 0)
{
lean_object* v___x_1847_; 
v___x_1847_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0___closed__0));
return v___x_1847_;
}
else
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_Name_fromJson_x3f(v_x_1846_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1848_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1848_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1865_; 
v_a_1857_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1859_ = v___x_1848_;
v_isShared_1860_ = v_isSharedCheck_1865_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1848_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1865_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1863_; 
v___x_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1861_, 0, v_a_1857_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1861_);
v___x_1863_ = v___x_1859_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_fromJson_x3f(lean_object* v_json_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_Json_getObj_x3f(v_json_1868_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1869_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1879_; 
v_a_1878_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1878_);
lean_dec_ref(v___x_1869_);
v___x_1879_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_a_1878_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec(v_a_1878_);
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1879_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1879_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
else
{
lean_object* v_a_1888_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v_a_1892_; lean_object* v___y_1914_; lean_object* v_a_1915_; lean_object* v___y_1941_; lean_object* v_a_1944_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v_a_1888_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_a_1888_);
lean_dec_ref(v___x_1879_);
v___x_1971_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_1972_ = l_Lake_JsonObject_getJson_x3f(v_a_1878_, v___x_1971_);
if (lean_obj_tag(v___x_1972_) == 0)
{
goto v___jp_1969_;
}
else
{
lean_object* v_val_1973_; lean_object* v___x_1974_; 
v_val_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_val_1973_);
lean_dec_ref(v___x_1972_);
v___x_1974_ = l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0(v_val_1973_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1984_; 
lean_dec(v_a_1888_);
lean_dec(v_a_1878_);
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_1984_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1984_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1982_; 
v___x_1979_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__1));
v___x_1980_ = lean_string_append(v___x_1979_, v_a_1975_);
lean_dec(v_a_1975_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1980_);
v___x_1982_ = v___x_1977_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1980_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
else
{
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_dec(v_a_1888_);
lean_dec(v_a_1878_);
v_a_1985_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1974_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1974_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set_tag(v___x_1987_, 0);
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
else
{
lean_object* v_a_1993_; 
v_a_1993_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1993_);
lean_dec_ref(v___x_1974_);
if (lean_obj_tag(v_a_1993_) == 0)
{
goto v___jp_1969_;
}
else
{
lean_object* v_val_1994_; 
v_val_1994_ = lean_ctor_get(v_a_1993_, 0);
lean_inc(v_val_1994_);
lean_dec_ref(v_a_1993_);
v_a_1944_ = v_val_1994_;
goto v___jp_1943_;
}
}
}
}
v___jp_1889_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1894_, 0, v_a_1888_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
v___x_1895_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(v___x_1894_, v_a_1878_);
lean_dec(v_a_1878_);
lean_dec_ref(v___x_1894_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
lean_dec(v_a_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1895_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1895_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1912_; 
v_a_1904_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1906_ = v___x_1895_;
v_isShared_1907_ = v_isSharedCheck_1912_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1895_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1912_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1908_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1908_, 0, v___y_1890_);
lean_ctor_set(v___x_1908_, 1, v___y_1891_);
lean_ctor_set(v___x_1908_, 2, v_a_1892_);
lean_ctor_set(v___x_1908_, 3, v_a_1904_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 0, v___x_1908_);
v___x_1910_ = v___x_1906_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
v___jp_1913_:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__5));
v___x_1917_ = l_Lake_JsonObject_getJson_x3f(v_a_1878_, v___x_1916_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v___x_1918_; 
v___x_1918_ = lean_box(0);
v___y_1890_ = v___y_1914_;
v___y_1891_ = v_a_1915_;
v_a_1892_ = v___x_1918_;
goto v___jp_1889_;
}
else
{
lean_object* v_val_1919_; lean_object* v___x_1920_; 
v_val_1919_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_val_1919_);
lean_dec_ref(v___x_1917_);
v___x_1920_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1919_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1930_; 
lean_dec_ref(v_a_1915_);
lean_dec(v___y_1914_);
lean_dec(v_a_1888_);
lean_dec(v_a_1878_);
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1923_ = v___x_1920_;
v_isShared_1924_ = v_isSharedCheck_1930_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1930_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1925_ = ((lean_object*)(l_Lake_Manifest_fromJson_x3f___closed__0));
v___x_1926_ = lean_string_append(v___x_1925_, v_a_1921_);
lean_dec(v_a_1921_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1926_);
v___x_1928_ = v___x_1923_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
else
{
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec_ref(v_a_1915_);
lean_dec(v___y_1914_);
lean_dec(v_a_1888_);
lean_dec(v_a_1878_);
v_a_1931_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1920_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1920_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set_tag(v___x_1933_, 0);
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
else
{
lean_object* v_a_1939_; 
v_a_1939_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1939_);
lean_dec_ref(v___x_1920_);
v___y_1890_ = v___y_1914_;
v___y_1891_ = v_a_1915_;
v_a_1892_ = v_a_1939_;
goto v___jp_1889_;
}
}
}
}
v___jp_1940_:
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Lake_defaultLakeDir;
v___y_1914_ = v___y_1941_;
v_a_1915_ = v___x_1942_;
goto v___jp_1913_;
}
v___jp_1943_:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__4));
v___x_1946_ = l_Lake_JsonObject_getJson_x3f(v_a_1878_, v___x_1945_);
if (lean_obj_tag(v___x_1946_) == 0)
{
v___y_1941_ = v_a_1944_;
goto v___jp_1940_;
}
else
{
lean_object* v_val_1947_; lean_object* v___x_1948_; 
v_val_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_val_1947_);
lean_dec_ref(v___x_1946_);
v___x_1948_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1947_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1958_; 
lean_dec(v_a_1944_);
lean_dec(v_a_1888_);
lean_dec(v_a_1878_);
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1951_ = v___x_1948_;
v_isShared_1952_ = v_isSharedCheck_1958_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1958_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1956_; 
v___x_1953_ = ((lean_object*)(l_Lake_Manifest_fromJson_x3f___closed__1));
v___x_1954_ = lean_string_append(v___x_1953_, v_a_1949_);
lean_dec(v_a_1949_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1954_);
v___x_1956_ = v___x_1951_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1954_);
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
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec(v_a_1944_);
lean_dec(v_a_1888_);
lean_dec(v_a_1878_);
v_a_1959_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1948_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1948_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
lean_ctor_set_tag(v___x_1961_, 0);
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
else
{
lean_object* v_a_1967_; 
v_a_1967_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1967_);
lean_dec_ref(v___x_1948_);
if (lean_obj_tag(v_a_1967_) == 0)
{
v___y_1941_ = v_a_1944_;
goto v___jp_1940_;
}
else
{
lean_object* v_val_1968_; 
v_val_1968_ = lean_ctor_get(v_a_1967_, 0);
lean_inc(v_val_1968_);
lean_dec_ref(v_a_1967_);
v___y_1914_ = v_a_1944_;
v_a_1915_ = v_val_1968_;
goto v___jp_1913_;
}
}
}
}
}
v___jp_1969_:
{
lean_object* v___x_1970_; 
v___x_1970_ = lean_box(0);
v_a_1944_ = v___x_1970_;
goto v___jp_1943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_parse(lean_object* v_data_1998_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_Json_parse(v_data_1998_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2009_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2002_ = v___x_1999_;
v_isShared_2003_ = v_isSharedCheck_2009_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1999_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2009_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2004_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2005_ = lean_string_append(v___x_2004_, v_a_2000_);
lean_dec(v_a_2000_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v___x_2005_);
v___x_2007_ = v___x_2002_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2011_; 
v_a_2010_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2010_);
lean_dec_ref(v___x_1999_);
v___x_2011_ = l_Lake_Manifest_fromJson_x3f(v_a_2010_);
return v___x_2011_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load(lean_object* v_file_2013_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = l_IO_FS_readFile(v_file_2013_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2044_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2044_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2044_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v_a_2021_; lean_object* v___x_2029_; 
v___x_2029_ = l_Lean_Json_parse(v_a_2016_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref(v___x_2029_);
v___x_2031_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2032_ = lean_string_append(v___x_2031_, v_a_2030_);
lean_dec(v_a_2030_);
v_a_2021_ = v___x_2032_;
goto v___jp_2020_;
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2034_; 
v_a_2033_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2033_);
lean_dec_ref(v___x_2029_);
v___x_2034_ = l_Lake_Manifest_fromJson_x3f(v_a_2033_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref(v___x_2034_);
v_a_2021_ = v_a_2035_;
goto v___jp_2020_;
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_del_object(v___x_2018_);
lean_dec_ref(v_file_2013_);
v_a_2036_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2034_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2034_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
lean_ctor_set_tag(v___x_2038_, 0);
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
v___jp_2020_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2022_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2023_ = lean_string_append(v_file_2013_, v___x_2022_);
v___x_2024_ = lean_string_append(v___x_2023_, v_a_2021_);
lean_dec_ref(v_a_2021_);
v___x_2025_ = lean_mk_io_user_error(v___x_2024_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set_tag(v___x_2018_, 1);
lean_ctor_set(v___x_2018_, 0, v___x_2025_);
v___x_2027_ = v___x_2018_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec_ref(v_file_2013_);
v_a_2045_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2015_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2015_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load___boxed(lean_object* v_file_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lake_Manifest_load(v_file_2053_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f(lean_object* v_file_2056_){
_start:
{
lean_object* v_a_2059_; lean_object* v___x_2063_; 
v___x_2063_ = l_IO_FS_readFile(v_file_2056_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2092_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2066_ = v___x_2063_;
v_isShared_2067_ = v_isSharedCheck_2092_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2063_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2092_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v_a_2069_; lean_object* v___x_2074_; 
v___x_2074_ = l_Lean_Json_parse(v_a_2064_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_del_object(v___x_2066_);
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2075_);
lean_dec_ref(v___x_2074_);
v___x_2076_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2077_ = lean_string_append(v___x_2076_, v_a_2075_);
lean_dec(v_a_2075_);
v_a_2069_ = v___x_2077_;
goto v___jp_2068_;
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2079_; 
v_a_2078_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2078_);
lean_dec_ref(v___x_2074_);
v___x_2079_ = l_Lake_Manifest_fromJson_x3f(v_a_2078_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; 
lean_del_object(v___x_2066_);
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2080_);
lean_dec_ref(v___x_2079_);
v_a_2069_ = v_a_2080_;
goto v___jp_2068_;
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2091_; 
lean_dec_ref(v_file_2056_);
v_a_2081_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2083_ = v___x_2079_;
v_isShared_2084_ = v_isSharedCheck_2091_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2079_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2091_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
lean_object* v___x_2088_; 
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 0, v___x_2086_);
v___x_2088_ = v___x_2066_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
}
v___jp_2068_:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2070_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2071_ = lean_string_append(v_file_2056_, v___x_2070_);
v___x_2072_ = lean_string_append(v___x_2071_, v_a_2069_);
lean_dec_ref(v_a_2069_);
v___x_2073_ = lean_mk_io_user_error(v___x_2072_);
v_a_2059_ = v___x_2073_;
goto v___jp_2058_;
}
}
}
else
{
lean_object* v_a_2093_; 
lean_dec_ref(v_file_2056_);
v_a_2093_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2093_);
lean_dec_ref(v___x_2063_);
v_a_2059_ = v_a_2093_;
goto v___jp_2058_;
}
v___jp_2058_:
{
if (lean_obj_tag(v_a_2059_) == 11)
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
lean_dec_ref(v_a_2059_);
v___x_2060_ = lean_box(0);
v___x_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
return v___x_2061_;
}
else
{
lean_object* v___x_2062_; 
v___x_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2062_, 0, v_a_2059_);
return v___x_2062_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f___boxed(lean_object* v_file_2094_, lean_object* v_a_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Lake_Manifest_load_x3f(v_file_2094_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_save(lean_object* v_self_2097_, lean_object* v_manifestFile_2098_){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v_contents_2102_; uint32_t v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2100_ = l_Lake_Manifest_toJson(v_self_2097_);
v___x_2101_ = lean_unsigned_to_nat(80u);
v_contents_2102_ = l_Lean_Json_pretty(v___x_2100_, v___x_2101_);
v___x_2103_ = 10;
v___x_2104_ = lean_string_push(v_contents_2102_, v___x_2103_);
v___x_2105_ = l_IO_FS_writeFile(v_manifestFile_2098_, v___x_2104_);
lean_dec_ref(v___x_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_save___boxed(lean_object* v_self_2106_, lean_object* v_manifestFile_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lake_Manifest_save(v_self_2106_, v_manifestFile_2107_);
lean_dec_ref(v_manifestFile_2107_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_decodeEntries(lean_object* v_data_2110_){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Lean_Json_getObj_x3f(v_data_2110_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2111_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2111_);
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
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2120_; lean_object* v___x_2121_; 
v_a_2120_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2120_);
lean_dec_ref(v___x_2111_);
v___x_2121_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_a_2120_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec(v_a_2120_);
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v_a_2130_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2130_);
lean_dec_ref(v___x_2121_);
v___x_2131_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2132_, 0, v_a_2130_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(v___x_2132_, v_a_2120_);
lean_dec(v_a_2120_);
lean_dec_ref(v___x_2132_);
return v___x_2133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_parseEntries(lean_object* v_data_2134_){
_start:
{
lean_object* v___x_2135_; 
v___x_2135_ = l_Lean_Json_parse(v_data_2134_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2145_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2145_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2145_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2140_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2141_ = lean_string_append(v___x_2140_, v_a_2136_);
lean_dec(v_a_2136_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2141_);
v___x_2143_ = v___x_2138_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2147_; 
v_a_2146_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2146_);
lean_dec_ref(v___x_2135_);
v___x_2147_ = l_Lake_Manifest_decodeEntries(v_a_2146_);
return v___x_2147_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_loadEntries(lean_object* v_file_2148_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = l_IO_FS_readFile(v_file_2148_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2179_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2153_ = v___x_2150_;
v_isShared_2154_ = v_isSharedCheck_2179_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2150_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2179_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v_a_2156_; lean_object* v___x_2164_; 
v___x_2164_ = l_Lean_Json_parse(v_a_2151_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref(v___x_2164_);
v___x_2166_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2167_ = lean_string_append(v___x_2166_, v_a_2165_);
lean_dec(v_a_2165_);
v_a_2156_ = v___x_2167_;
goto v___jp_2155_;
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2169_; 
v_a_2168_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2168_);
lean_dec_ref(v___x_2164_);
v___x_2169_ = l_Lake_Manifest_decodeEntries(v_a_2168_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref(v___x_2169_);
v_a_2156_ = v_a_2170_;
goto v___jp_2155_;
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_del_object(v___x_2153_);
lean_dec_ref(v_file_2148_);
v_a_2171_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2169_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2169_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
lean_ctor_set_tag(v___x_2173_, 0);
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
v___jp_2155_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2157_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2158_ = lean_string_append(v_file_2148_, v___x_2157_);
v___x_2159_ = lean_string_append(v___x_2158_, v_a_2156_);
lean_dec_ref(v_a_2156_);
v___x_2160_ = lean_mk_io_user_error(v___x_2159_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set_tag(v___x_2153_, 1);
lean_ctor_set(v___x_2153_, 0, v___x_2160_);
v___x_2162_ = v___x_2153_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec_ref(v_file_2148_);
v_a_2180_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2150_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2150_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_loadEntries___boxed(lean_object* v_file_2188_, lean_object* v_a_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Lake_Manifest_loadEntries(v_file_2188_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries(lean_object* v_file_2191_){
_start:
{
lean_object* v_a_2194_; lean_object* v___x_2203_; 
v___x_2203_ = l_IO_FS_readFile(v_file_2191_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2225_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2206_ = v___x_2203_;
v_isShared_2207_ = v_isSharedCheck_2225_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2225_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v_a_2209_; lean_object* v___x_2214_; 
v___x_2214_ = l_Lean_Json_parse(v_a_2204_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
lean_del_object(v___x_2206_);
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref(v___x_2214_);
v___x_2216_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2217_ = lean_string_append(v___x_2216_, v_a_2215_);
lean_dec(v_a_2215_);
v_a_2209_ = v___x_2217_;
goto v___jp_2208_;
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2219_; 
v_a_2218_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2218_);
lean_dec_ref(v___x_2214_);
v___x_2219_ = l_Lake_Manifest_decodeEntries(v_a_2218_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; 
lean_del_object(v___x_2206_);
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2220_);
lean_dec_ref(v___x_2219_);
v_a_2209_ = v_a_2220_;
goto v___jp_2208_;
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; 
lean_dec_ref(v_file_2191_);
v_a_2221_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2221_);
lean_dec_ref(v___x_2219_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v_a_2221_);
v___x_2223_ = v___x_2206_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2221_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
v___jp_2208_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2210_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
lean_inc_ref(v_file_2191_);
v___x_2211_ = lean_string_append(v_file_2191_, v___x_2210_);
v___x_2212_ = lean_string_append(v___x_2211_, v_a_2209_);
lean_dec_ref(v_a_2209_);
v___x_2213_ = lean_mk_io_user_error(v___x_2212_);
v_a_2194_ = v___x_2213_;
goto v___jp_2193_;
}
}
}
else
{
lean_object* v_a_2226_; 
v_a_2226_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_a_2226_);
lean_dec_ref(v___x_2203_);
v_a_2194_ = v_a_2226_;
goto v___jp_2193_;
}
v___jp_2193_:
{
if (lean_obj_tag(v_a_2194_) == 11)
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
lean_dec_ref(v_a_2194_);
lean_dec_ref(v_file_2191_);
v___x_2195_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__1));
v___x_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
return v___x_2196_;
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2197_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2198_ = lean_string_append(v_file_2191_, v___x_2197_);
v___x_2199_ = lean_io_error_to_string(v_a_2194_);
v___x_2200_ = lean_string_append(v___x_2198_, v___x_2199_);
lean_dec_ref(v___x_2199_);
v___x_2201_ = lean_mk_io_user_error(v___x_2200_);
v___x_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
return v___x_2202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries___boxed(lean_object* v_file_2227_, lean_object* v_a_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Lake_Manifest_tryLoadEntries(v_file_2227_);
return v_res_2229_;
}
}
static lean_object* _init_l_Lake_Manifest_saveEntries___closed__0(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2230_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__2, &l_Lake_Manifest_toJson___closed__2_once, _init_l_Lake_Manifest_toJson___closed__2);
v___x_2231_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8));
v___x_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v___x_2230_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries(lean_object* v_file_2233_, lean_object* v_entries_2234_){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v_contents_2245_; uint32_t v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2236_ = lean_obj_once(&l_Lake_Manifest_saveEntries___closed__0, &l_Lake_Manifest_saveEntries___closed__0_once, _init_l_Lake_Manifest_saveEntries___closed__0);
v___x_2237_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__6));
v___x_2238_ = l_Array_toJson___at___00Lake_Manifest_toJson_spec__0(v_entries_2234_);
v___x_2239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2237_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
v___x_2240_ = lean_box(0);
v___x_2241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2239_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
v___x_2242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2236_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
v___x_2243_ = l_Lean_Json_mkObj(v___x_2242_);
v___x_2244_ = lean_unsigned_to_nat(80u);
v_contents_2245_ = l_Lean_Json_pretty(v___x_2243_, v___x_2244_);
v___x_2246_ = 10;
v___x_2247_ = lean_string_push(v_contents_2245_, v___x_2246_);
v___x_2248_ = l_IO_FS_writeFile(v_file_2233_, v___x_2247_);
lean_dec_ref(v___x_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries___boxed(lean_object* v_file_2249_, lean_object* v_entries_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lake_Manifest_saveEntries(v_file_2249_, v_entries_2250_);
lean_dec_ref(v_file_2249_);
return v_res_2252_;
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
