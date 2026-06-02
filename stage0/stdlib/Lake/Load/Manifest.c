// Lean compiler output
// Module: Lake.Load.Manifest
// Imports: public import Lake.Util.Version public import Lake.Config.Defaults public import Lake.Util.Git import Lake.Util.Error public import Lake.Util.FilePath import Lake.Util.JsonObject import Init.Data.Option.Coe
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
uint8_t lean_string_compare(lean_object*, lean_object*);
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
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
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
lean_dec_ref_known(v_t_15_, 3);
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
lean_dec_ref_known(v_t_15_, 6);
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
lean_dec_ref_known(v_x_106_, 5);
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
lean_dec_ref_known(v___x_120_, 1);
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
lean_dec_ref_known(v___x_139_, 1);
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
lean_dec_ref_known(v_x_155_, 1);
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
lean_dec_ref_known(v___x_229_, 1);
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
lean_dec_ref_known(v___x_240_, 1);
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
lean_dec_ref_known(v___x_252_, 1);
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
lean_dec_ref_known(v___x_264_, 1);
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
lean_dec_ref_known(v___x_276_, 1);
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
lean_dec_ref_known(v___x_288_, 1);
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
lean_dec_ref_known(v___x_300_, 1);
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
lean_dec_ref_known(v___x_312_, 1);
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
lean_dec_ref_known(v___x_345_, 1);
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
lean_dec_ref_known(v___x_357_, 1);
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
lean_dec_ref_known(v___x_369_, 1);
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
lean_dec_ref_known(v___x_381_, 1);
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
v___x_443_ = lean_unsigned_to_nat(182u);
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
v___x_449_ = lean_unsigned_to_nat(183u);
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
v___x_457_ = lean_unsigned_to_nat(276u);
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
v___x_463_ = lean_unsigned_to_nat(277u);
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
lean_object* v_size_470_; lean_object* v_k_471_; lean_object* v_v_472_; lean_object* v_l_473_; lean_object* v_r_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_830_; 
v_size_470_ = lean_ctor_get(v_t_469_, 0);
v_k_471_ = lean_ctor_get(v_t_469_, 1);
v_v_472_ = lean_ctor_get(v_t_469_, 2);
v_l_473_ = lean_ctor_get(v_t_469_, 3);
v_r_474_ = lean_ctor_get(v_t_469_, 4);
v_isSharedCheck_830_ = !lean_is_exclusive(v_t_469_);
if (v_isSharedCheck_830_ == 0)
{
v___x_476_ = v_t_469_;
v_isShared_477_ = v_isSharedCheck_830_;
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
v_isShared_477_ = v_isSharedCheck_830_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
uint8_t v___x_478_; 
v___x_478_ = lean_string_compare(v_k_467_, v_k_471_);
switch(v___x_478_)
{
case 0:
{
lean_object* v___x_479_; 
lean_dec(v_size_470_);
v___x_479_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(v_k_467_, v_v_468_, v_l_473_);
if (lean_obj_tag(v_r_474_) == 0)
{
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_size_480_; lean_object* v_size_481_; lean_object* v_k_482_; lean_object* v_v_483_; lean_object* v_l_484_; lean_object* v_r_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_size_480_ = lean_ctor_get(v_r_474_, 0);
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
v___x_490_ = lean_nat_add(v___x_489_, v_size_481_);
lean_dec(v_size_481_);
v___x_491_ = lean_nat_add(v___x_490_, v_size_480_);
lean_dec(v___x_490_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 3, v___x_479_);
lean_ctor_set(v___x_476_, 0, v___x_491_);
v___x_493_ = v___x_476_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_494_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_494_, 3, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_494_, 4, v_r_474_);
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
lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_566_; 
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_566_ == 0)
{
lean_object* v_unused_567_; lean_object* v_unused_568_; lean_object* v_unused_569_; lean_object* v_unused_570_; lean_object* v_unused_571_; 
v_unused_567_ = lean_ctor_get(v___x_479_, 4);
lean_dec(v_unused_567_);
v_unused_568_ = lean_ctor_get(v___x_479_, 3);
lean_dec(v_unused_568_);
v_unused_569_ = lean_ctor_get(v___x_479_, 2);
lean_dec(v_unused_569_);
v_unused_570_ = lean_ctor_get(v___x_479_, 1);
lean_dec(v_unused_570_);
v_unused_571_ = lean_ctor_get(v___x_479_, 0);
lean_dec(v_unused_571_);
v___x_496_ = v___x_479_;
v_isShared_497_ = v_isSharedCheck_566_;
goto v_resetjp_495_;
}
else
{
lean_dec(v___x_479_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_566_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
if (lean_obj_tag(v_l_484_) == 0)
{
if (lean_obj_tag(v_r_485_) == 0)
{
lean_object* v_size_498_; lean_object* v_size_499_; lean_object* v_k_500_; lean_object* v_v_501_; lean_object* v_l_502_; lean_object* v_r_503_; lean_object* v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v_size_498_ = lean_ctor_get(v_l_484_, 0);
v_size_499_ = lean_ctor_get(v_r_485_, 0);
v_k_500_ = lean_ctor_get(v_r_485_, 1);
v_v_501_ = lean_ctor_get(v_r_485_, 2);
v_l_502_ = lean_ctor_get(v_r_485_, 3);
v_r_503_ = lean_ctor_get(v_r_485_, 4);
v___x_504_ = lean_unsigned_to_nat(2u);
v___x_505_ = lean_nat_mul(v___x_504_, v_size_498_);
v___x_506_ = lean_nat_dec_lt(v_size_499_, v___x_505_);
lean_dec(v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_536_; 
lean_inc(v_r_503_);
lean_inc(v_l_502_);
lean_inc(v_v_501_);
lean_inc(v_k_500_);
v_isSharedCheck_536_ = !lean_is_exclusive(v_r_485_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; lean_object* v_unused_538_; lean_object* v_unused_539_; lean_object* v_unused_540_; lean_object* v_unused_541_; 
v_unused_537_ = lean_ctor_get(v_r_485_, 4);
lean_dec(v_unused_537_);
v_unused_538_ = lean_ctor_get(v_r_485_, 3);
lean_dec(v_unused_538_);
v_unused_539_ = lean_ctor_get(v_r_485_, 2);
lean_dec(v_unused_539_);
v_unused_540_ = lean_ctor_get(v_r_485_, 1);
lean_dec(v_unused_540_);
v_unused_541_ = lean_ctor_get(v_r_485_, 0);
lean_dec(v_unused_541_);
v___x_508_ = v_r_485_;
v_isShared_509_ = v_isSharedCheck_536_;
goto v_resetjp_507_;
}
else
{
lean_dec(v_r_485_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_536_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___x_524_; lean_object* v___y_526_; 
v___x_510_ = lean_unsigned_to_nat(1u);
v___x_511_ = lean_nat_add(v___x_510_, v_size_481_);
lean_dec(v_size_481_);
v___x_512_ = lean_nat_add(v___x_511_, v_size_480_);
lean_dec(v___x_511_);
v___x_524_ = lean_nat_add(v___x_510_, v_size_498_);
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
v___jp_513_:
{
lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_517_ = lean_nat_add(v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec(v___y_515_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 4, v_r_474_);
lean_ctor_set(v___x_508_, 3, v_r_503_);
lean_ctor_set(v___x_508_, 2, v_v_472_);
lean_ctor_set(v___x_508_, 1, v_k_471_);
lean_ctor_set(v___x_508_, 0, v___x_517_);
v___x_519_ = v___x_508_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_523_, 3, v_r_503_);
lean_ctor_set(v_reuseFailAlloc_523_, 4, v_r_474_);
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
lean_ctor_set(v___x_496_, 2, v_v_501_);
lean_ctor_set(v___x_496_, 1, v_k_500_);
lean_ctor_set(v___x_496_, 0, v___x_512_);
v___x_521_ = v___x_496_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_k_500_);
lean_ctor_set(v_reuseFailAlloc_522_, 2, v_v_501_);
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
v___jp_525_:
{
lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_527_ = lean_nat_add(v___x_524_, v___y_526_);
lean_dec(v___y_526_);
lean_dec(v___x_524_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v_l_502_);
lean_ctor_set(v___x_476_, 3, v_l_484_);
lean_ctor_set(v___x_476_, 2, v_v_483_);
lean_ctor_set(v___x_476_, 1, v_k_482_);
lean_ctor_set(v___x_476_, 0, v___x_527_);
v___x_529_ = v___x_476_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_k_482_);
lean_ctor_set(v_reuseFailAlloc_533_, 2, v_v_483_);
lean_ctor_set(v_reuseFailAlloc_533_, 3, v_l_484_);
lean_ctor_set(v_reuseFailAlloc_533_, 4, v_l_502_);
v___x_529_ = v_reuseFailAlloc_533_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_530_; 
v___x_530_ = lean_nat_add(v___x_510_, v_size_480_);
if (lean_obj_tag(v_r_503_) == 0)
{
lean_object* v_size_531_; 
v_size_531_ = lean_ctor_get(v_r_503_, 0);
lean_inc(v_size_531_);
v___y_514_ = v___x_529_;
v___y_515_ = v___x_530_;
v___y_516_ = v_size_531_;
goto v___jp_513_;
}
else
{
lean_object* v___x_532_; 
v___x_532_ = lean_unsigned_to_nat(0u);
v___y_514_ = v___x_529_;
v___y_515_ = v___x_530_;
v___y_516_ = v___x_532_;
goto v___jp_513_;
}
}
}
}
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_548_; 
lean_del_object(v___x_476_);
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = lean_nat_add(v___x_542_, v_size_481_);
lean_dec(v_size_481_);
v___x_544_ = lean_nat_add(v___x_543_, v_size_480_);
lean_dec(v___x_543_);
v___x_545_ = lean_nat_add(v___x_542_, v_size_480_);
v___x_546_ = lean_nat_add(v___x_545_, v_size_499_);
lean_dec(v___x_545_);
lean_inc_ref(v_r_474_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 4, v_r_474_);
lean_ctor_set(v___x_496_, 3, v_r_485_);
lean_ctor_set(v___x_496_, 2, v_v_472_);
lean_ctor_set(v___x_496_, 1, v_k_471_);
lean_ctor_set(v___x_496_, 0, v___x_546_);
v___x_548_ = v___x_496_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_r_485_);
lean_ctor_set(v_reuseFailAlloc_561_, 4, v_r_474_);
v___x_548_ = v_reuseFailAlloc_561_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
v_isSharedCheck_555_ = !lean_is_exclusive(v_r_474_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; lean_object* v_unused_557_; lean_object* v_unused_558_; lean_object* v_unused_559_; lean_object* v_unused_560_; 
v_unused_556_ = lean_ctor_get(v_r_474_, 4);
lean_dec(v_unused_556_);
v_unused_557_ = lean_ctor_get(v_r_474_, 3);
lean_dec(v_unused_557_);
v_unused_558_ = lean_ctor_get(v_r_474_, 2);
lean_dec(v_unused_558_);
v_unused_559_ = lean_ctor_get(v_r_474_, 1);
lean_dec(v_unused_559_);
v_unused_560_ = lean_ctor_get(v_r_474_, 0);
lean_dec(v_unused_560_);
v___x_550_ = v_r_474_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_dec(v_r_474_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 4, v___x_548_);
lean_ctor_set(v___x_550_, 3, v_l_484_);
lean_ctor_set(v___x_550_, 2, v_v_483_);
lean_ctor_set(v___x_550_, 1, v_k_482_);
lean_ctor_set(v___x_550_, 0, v___x_544_);
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_k_482_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_v_483_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v_l_484_);
lean_ctor_set(v_reuseFailAlloc_554_, 4, v___x_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; 
lean_dec_ref_known(v_l_484_, 5);
lean_del_object(v___x_496_);
lean_dec(v_v_483_);
lean_dec(v_k_482_);
lean_dec(v_size_481_);
lean_dec_ref_known(v_r_474_, 5);
lean_del_object(v___x_476_);
lean_dec(v_v_472_);
lean_dec(v_k_471_);
v___x_562_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3);
v___x_563_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v___x_562_);
return v___x_563_;
}
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; 
lean_del_object(v___x_496_);
lean_dec(v_r_485_);
lean_dec(v_v_483_);
lean_dec(v_k_482_);
lean_dec(v_size_481_);
lean_dec_ref_known(v_r_474_, 5);
lean_del_object(v___x_476_);
lean_dec(v_v_472_);
lean_dec(v_k_471_);
v___x_564_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4);
v___x_565_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v___x_564_);
return v___x_565_;
}
}
}
}
else
{
lean_object* v_size_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v_size_572_ = lean_ctor_get(v_r_474_, 0);
v___x_573_ = lean_unsigned_to_nat(1u);
v___x_574_ = lean_nat_add(v___x_573_, v_size_572_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 3, v___x_479_);
lean_ctor_set(v___x_476_, 0, v___x_574_);
v___x_576_ = v___x_476_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_577_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_577_, 3, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_577_, 4, v_r_474_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
else
{
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_l_578_; 
v_l_578_ = lean_ctor_get(v___x_479_, 3);
lean_inc(v_l_578_);
if (lean_obj_tag(v_l_578_) == 0)
{
lean_object* v_r_579_; 
v_r_579_ = lean_ctor_get(v___x_479_, 4);
lean_inc(v_r_579_);
if (lean_obj_tag(v_r_579_) == 0)
{
lean_object* v_size_580_; lean_object* v_k_581_; lean_object* v_v_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_596_; 
v_size_580_ = lean_ctor_get(v___x_479_, 0);
v_k_581_ = lean_ctor_get(v___x_479_, 1);
v_v_582_ = lean_ctor_get(v___x_479_, 2);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; lean_object* v_unused_598_; 
v_unused_597_ = lean_ctor_get(v___x_479_, 4);
lean_dec(v_unused_597_);
v_unused_598_ = lean_ctor_get(v___x_479_, 3);
lean_dec(v_unused_598_);
v___x_584_ = v___x_479_;
v_isShared_585_ = v_isSharedCheck_596_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_v_582_);
lean_inc(v_k_581_);
lean_inc(v_size_580_);
lean_dec(v___x_479_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_596_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v_size_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_591_; 
v_size_586_ = lean_ctor_get(v_r_579_, 0);
v___x_587_ = lean_unsigned_to_nat(1u);
v___x_588_ = lean_nat_add(v___x_587_, v_size_580_);
lean_dec(v_size_580_);
v___x_589_ = lean_nat_add(v___x_587_, v_size_586_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 4, v_r_474_);
lean_ctor_set(v___x_584_, 3, v_r_579_);
lean_ctor_set(v___x_584_, 2, v_v_472_);
lean_ctor_set(v___x_584_, 1, v_k_471_);
lean_ctor_set(v___x_584_, 0, v___x_589_);
v___x_591_ = v___x_584_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_589_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_595_, 3, v_r_579_);
lean_ctor_set(v_reuseFailAlloc_595_, 4, v_r_474_);
v___x_591_ = v_reuseFailAlloc_595_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_593_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_591_);
lean_ctor_set(v___x_476_, 3, v_l_578_);
lean_ctor_set(v___x_476_, 2, v_v_582_);
lean_ctor_set(v___x_476_, 1, v_k_581_);
lean_ctor_set(v___x_476_, 0, v___x_588_);
v___x_593_ = v___x_476_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_k_581_);
lean_ctor_set(v_reuseFailAlloc_594_, 2, v_v_582_);
lean_ctor_set(v_reuseFailAlloc_594_, 3, v_l_578_);
lean_ctor_set(v_reuseFailAlloc_594_, 4, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
else
{
lean_object* v_k_599_; lean_object* v_v_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_612_; 
v_k_599_ = lean_ctor_get(v___x_479_, 1);
v_v_600_ = lean_ctor_get(v___x_479_, 2);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; lean_object* v_unused_614_; lean_object* v_unused_615_; 
v_unused_613_ = lean_ctor_get(v___x_479_, 4);
lean_dec(v_unused_613_);
v_unused_614_ = lean_ctor_get(v___x_479_, 3);
lean_dec(v_unused_614_);
v_unused_615_ = lean_ctor_get(v___x_479_, 0);
lean_dec(v_unused_615_);
v___x_602_ = v___x_479_;
v_isShared_603_ = v_isSharedCheck_612_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_v_600_);
lean_inc(v_k_599_);
lean_dec(v___x_479_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_612_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_604_ = lean_unsigned_to_nat(3u);
v___x_605_ = lean_unsigned_to_nat(1u);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 3, v_r_579_);
lean_ctor_set(v___x_602_, 2, v_v_472_);
lean_ctor_set(v___x_602_, 1, v_k_471_);
lean_ctor_set(v___x_602_, 0, v___x_605_);
v___x_607_ = v___x_602_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v_r_579_);
lean_ctor_set(v_reuseFailAlloc_611_, 4, v_r_579_);
v___x_607_ = v_reuseFailAlloc_611_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_609_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_607_);
lean_ctor_set(v___x_476_, 3, v_l_578_);
lean_ctor_set(v___x_476_, 2, v_v_600_);
lean_ctor_set(v___x_476_, 1, v_k_599_);
lean_ctor_set(v___x_476_, 0, v___x_604_);
v___x_609_ = v___x_476_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_k_599_);
lean_ctor_set(v_reuseFailAlloc_610_, 2, v_v_600_);
lean_ctor_set(v_reuseFailAlloc_610_, 3, v_l_578_);
lean_ctor_set(v_reuseFailAlloc_610_, 4, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
else
{
lean_object* v_r_616_; 
v_r_616_ = lean_ctor_get(v___x_479_, 4);
lean_inc(v_r_616_);
if (lean_obj_tag(v_r_616_) == 0)
{
lean_object* v_k_617_; lean_object* v_v_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_642_; 
v_k_617_ = lean_ctor_get(v___x_479_, 1);
v_v_618_ = lean_ctor_get(v___x_479_, 2);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; lean_object* v_unused_644_; lean_object* v_unused_645_; 
v_unused_643_ = lean_ctor_get(v___x_479_, 4);
lean_dec(v_unused_643_);
v_unused_644_ = lean_ctor_get(v___x_479_, 3);
lean_dec(v_unused_644_);
v_unused_645_ = lean_ctor_get(v___x_479_, 0);
lean_dec(v_unused_645_);
v___x_620_ = v___x_479_;
v_isShared_621_ = v_isSharedCheck_642_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_v_618_);
lean_inc(v_k_617_);
lean_dec(v___x_479_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_642_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v_k_622_; lean_object* v_v_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_638_; 
v_k_622_ = lean_ctor_get(v_r_616_, 1);
v_v_623_ = lean_ctor_get(v_r_616_, 2);
v_isSharedCheck_638_ = !lean_is_exclusive(v_r_616_);
if (v_isSharedCheck_638_ == 0)
{
lean_object* v_unused_639_; lean_object* v_unused_640_; lean_object* v_unused_641_; 
v_unused_639_ = lean_ctor_get(v_r_616_, 4);
lean_dec(v_unused_639_);
v_unused_640_ = lean_ctor_get(v_r_616_, 3);
lean_dec(v_unused_640_);
v_unused_641_ = lean_ctor_get(v_r_616_, 0);
lean_dec(v_unused_641_);
v___x_625_ = v_r_616_;
v_isShared_626_ = v_isSharedCheck_638_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_v_623_);
lean_inc(v_k_622_);
lean_dec(v_r_616_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_638_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_630_; 
v___x_627_ = lean_unsigned_to_nat(3u);
v___x_628_ = lean_unsigned_to_nat(1u);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 4, v_l_578_);
lean_ctor_set(v___x_625_, 3, v_l_578_);
lean_ctor_set(v___x_625_, 2, v_v_618_);
lean_ctor_set(v___x_625_, 1, v_k_617_);
lean_ctor_set(v___x_625_, 0, v___x_628_);
v___x_630_ = v___x_625_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_k_617_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_v_618_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v_l_578_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v_l_578_);
v___x_630_ = v_reuseFailAlloc_637_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_632_; 
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 4, v_l_578_);
lean_ctor_set(v___x_620_, 2, v_v_472_);
lean_ctor_set(v___x_620_, 1, v_k_471_);
lean_ctor_set(v___x_620_, 0, v___x_628_);
v___x_632_ = v___x_620_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v_l_578_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v_l_578_);
v___x_632_ = v_reuseFailAlloc_636_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_634_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_632_);
lean_ctor_set(v___x_476_, 3, v___x_630_);
lean_ctor_set(v___x_476_, 2, v_v_623_);
lean_ctor_set(v___x_476_, 1, v_k_622_);
lean_ctor_set(v___x_476_, 0, v___x_627_);
v___x_634_ = v___x_476_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_k_622_);
lean_ctor_set(v_reuseFailAlloc_635_, 2, v_v_623_);
lean_ctor_set(v_reuseFailAlloc_635_, 3, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_635_, 4, v___x_632_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
}
}
else
{
lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_646_ = lean_unsigned_to_nat(2u);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v_r_616_);
lean_ctor_set(v___x_476_, 3, v___x_479_);
lean_ctor_set(v___x_476_, 0, v___x_646_);
v___x_648_ = v___x_476_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_649_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_649_, 3, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_649_, 4, v_r_616_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
else
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = lean_unsigned_to_nat(1u);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_479_);
lean_ctor_set(v___x_476_, 3, v___x_479_);
lean_ctor_set(v___x_476_, 0, v___x_650_);
v___x_652_ = v___x_476_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_653_, 3, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_653_, 4, v___x_479_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
case 1:
{
lean_object* v___x_655_; 
lean_dec(v_v_472_);
lean_dec(v_k_471_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 2, v_v_468_);
lean_ctor_set(v___x_476_, 1, v_k_467_);
v___x_655_ = v___x_476_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_size_470_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_k_467_);
lean_ctor_set(v_reuseFailAlloc_656_, 2, v_v_468_);
lean_ctor_set(v_reuseFailAlloc_656_, 3, v_l_473_);
lean_ctor_set(v_reuseFailAlloc_656_, 4, v_r_474_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
default: 
{
lean_object* v___x_657_; 
lean_dec(v_size_470_);
v___x_657_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(v_k_467_, v_v_468_, v_r_474_);
if (lean_obj_tag(v_l_473_) == 0)
{
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_size_658_; lean_object* v_size_659_; lean_object* v_k_660_; lean_object* v_v_661_; lean_object* v_l_662_; lean_object* v_r_663_; lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v_size_658_ = lean_ctor_get(v_l_473_, 0);
v_size_659_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_size_659_);
v_k_660_ = lean_ctor_get(v___x_657_, 1);
lean_inc(v_k_660_);
v_v_661_ = lean_ctor_get(v___x_657_, 2);
lean_inc(v_v_661_);
v_l_662_ = lean_ctor_get(v___x_657_, 3);
lean_inc(v_l_662_);
v_r_663_ = lean_ctor_get(v___x_657_, 4);
lean_inc(v_r_663_);
v___x_664_ = lean_unsigned_to_nat(3u);
v___x_665_ = lean_nat_mul(v___x_664_, v_size_658_);
v___x_666_ = lean_nat_dec_lt(v___x_665_, v_size_659_);
lean_dec(v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
lean_dec(v_r_663_);
lean_dec(v_l_662_);
lean_dec(v_v_661_);
lean_dec(v_k_660_);
v___x_667_ = lean_unsigned_to_nat(1u);
v___x_668_ = lean_nat_add(v___x_667_, v_size_658_);
v___x_669_ = lean_nat_add(v___x_668_, v_size_659_);
lean_dec(v_size_659_);
lean_dec(v___x_668_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_657_);
lean_ctor_set(v___x_476_, 0, v___x_669_);
v___x_671_ = v___x_476_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_672_, 3, v_l_473_);
lean_ctor_set(v_reuseFailAlloc_672_, 4, v___x_657_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
else
{
lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_742_; 
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; lean_object* v_unused_744_; lean_object* v_unused_745_; lean_object* v_unused_746_; lean_object* v_unused_747_; 
v_unused_743_ = lean_ctor_get(v___x_657_, 4);
lean_dec(v_unused_743_);
v_unused_744_ = lean_ctor_get(v___x_657_, 3);
lean_dec(v_unused_744_);
v_unused_745_ = lean_ctor_get(v___x_657_, 2);
lean_dec(v_unused_745_);
v_unused_746_ = lean_ctor_get(v___x_657_, 1);
lean_dec(v_unused_746_);
v_unused_747_ = lean_ctor_get(v___x_657_, 0);
lean_dec(v_unused_747_);
v___x_674_ = v___x_657_;
v_isShared_675_ = v_isSharedCheck_742_;
goto v_resetjp_673_;
}
else
{
lean_dec(v___x_657_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_742_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
if (lean_obj_tag(v_l_662_) == 0)
{
if (lean_obj_tag(v_r_663_) == 0)
{
lean_object* v_size_676_; lean_object* v_k_677_; lean_object* v_v_678_; lean_object* v_l_679_; lean_object* v_r_680_; lean_object* v_size_681_; lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v_size_676_ = lean_ctor_get(v_l_662_, 0);
v_k_677_ = lean_ctor_get(v_l_662_, 1);
v_v_678_ = lean_ctor_get(v_l_662_, 2);
v_l_679_ = lean_ctor_get(v_l_662_, 3);
v_r_680_ = lean_ctor_get(v_l_662_, 4);
v_size_681_ = lean_ctor_get(v_r_663_, 0);
v___x_682_ = lean_unsigned_to_nat(2u);
v___x_683_ = lean_nat_mul(v___x_682_, v_size_681_);
v___x_684_ = lean_nat_dec_lt(v_size_676_, v___x_683_);
lean_dec(v___x_683_);
if (v___x_684_ == 0)
{
lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_713_; 
lean_inc(v_r_680_);
lean_inc(v_l_679_);
lean_inc(v_v_678_);
lean_inc(v_k_677_);
v_isSharedCheck_713_ = !lean_is_exclusive(v_l_662_);
if (v_isSharedCheck_713_ == 0)
{
lean_object* v_unused_714_; lean_object* v_unused_715_; lean_object* v_unused_716_; lean_object* v_unused_717_; lean_object* v_unused_718_; 
v_unused_714_ = lean_ctor_get(v_l_662_, 4);
lean_dec(v_unused_714_);
v_unused_715_ = lean_ctor_get(v_l_662_, 3);
lean_dec(v_unused_715_);
v_unused_716_ = lean_ctor_get(v_l_662_, 2);
lean_dec(v_unused_716_);
v_unused_717_ = lean_ctor_get(v_l_662_, 1);
lean_dec(v_unused_717_);
v_unused_718_ = lean_ctor_get(v_l_662_, 0);
lean_dec(v_unused_718_);
v___x_686_ = v_l_662_;
v_isShared_687_ = v_isSharedCheck_713_;
goto v_resetjp_685_;
}
else
{
lean_dec(v_l_662_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_713_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_703_; 
v___x_688_ = lean_unsigned_to_nat(1u);
v___x_689_ = lean_nat_add(v___x_688_, v_size_658_);
v___x_690_ = lean_nat_add(v___x_689_, v_size_659_);
lean_dec(v_size_659_);
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
v___jp_691_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_695_ = lean_nat_add(v___y_693_, v___y_694_);
lean_dec(v___y_694_);
lean_dec(v___y_693_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 4, v_r_663_);
lean_ctor_set(v___x_686_, 3, v_r_680_);
lean_ctor_set(v___x_686_, 2, v_v_661_);
lean_ctor_set(v___x_686_, 1, v_k_660_);
lean_ctor_set(v___x_686_, 0, v___x_695_);
v___x_697_ = v___x_686_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_k_660_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_v_661_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_r_680_);
lean_ctor_set(v_reuseFailAlloc_701_, 4, v_r_663_);
v___x_697_ = v_reuseFailAlloc_701_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_699_; 
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 4, v___x_697_);
lean_ctor_set(v___x_674_, 3, v___y_692_);
lean_ctor_set(v___x_674_, 2, v_v_678_);
lean_ctor_set(v___x_674_, 1, v_k_677_);
lean_ctor_set(v___x_674_, 0, v___x_690_);
v___x_699_ = v___x_674_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_k_677_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_v_678_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v___y_692_);
lean_ctor_set(v_reuseFailAlloc_700_, 4, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
v___jp_702_:
{
lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_704_ = lean_nat_add(v___x_689_, v___y_703_);
lean_dec(v___y_703_);
lean_dec(v___x_689_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v_l_679_);
lean_ctor_set(v___x_476_, 0, v___x_704_);
v___x_706_ = v___x_476_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_710_, 3, v_l_473_);
lean_ctor_set(v_reuseFailAlloc_710_, 4, v_l_679_);
v___x_706_ = v_reuseFailAlloc_710_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_707_; 
v___x_707_ = lean_nat_add(v___x_688_, v_size_681_);
if (lean_obj_tag(v_r_680_) == 0)
{
lean_object* v_size_708_; 
v_size_708_ = lean_ctor_get(v_r_680_, 0);
lean_inc(v_size_708_);
v___y_692_ = v___x_706_;
v___y_693_ = v___x_707_;
v___y_694_ = v_size_708_;
goto v___jp_691_;
}
else
{
lean_object* v___x_709_; 
v___x_709_ = lean_unsigned_to_nat(0u);
v___y_692_ = v___x_706_;
v___y_693_ = v___x_707_;
v___y_694_ = v___x_709_;
goto v___jp_691_;
}
}
}
}
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
lean_del_object(v___x_476_);
v___x_719_ = lean_unsigned_to_nat(1u);
v___x_720_ = lean_nat_add(v___x_719_, v_size_658_);
v___x_721_ = lean_nat_add(v___x_720_, v_size_659_);
lean_dec(v_size_659_);
v___x_722_ = lean_nat_add(v___x_720_, v_size_676_);
lean_dec(v___x_720_);
lean_inc_ref(v_l_473_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 4, v_l_662_);
lean_ctor_set(v___x_674_, 3, v_l_473_);
lean_ctor_set(v___x_674_, 2, v_v_472_);
lean_ctor_set(v___x_674_, 1, v_k_471_);
lean_ctor_set(v___x_674_, 0, v___x_722_);
v___x_724_ = v___x_674_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_737_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_737_, 3, v_l_473_);
lean_ctor_set(v_reuseFailAlloc_737_, 4, v_l_662_);
v___x_724_ = v_reuseFailAlloc_737_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
v_isSharedCheck_731_ = !lean_is_exclusive(v_l_473_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; lean_object* v_unused_733_; lean_object* v_unused_734_; lean_object* v_unused_735_; lean_object* v_unused_736_; 
v_unused_732_ = lean_ctor_get(v_l_473_, 4);
lean_dec(v_unused_732_);
v_unused_733_ = lean_ctor_get(v_l_473_, 3);
lean_dec(v_unused_733_);
v_unused_734_ = lean_ctor_get(v_l_473_, 2);
lean_dec(v_unused_734_);
v_unused_735_ = lean_ctor_get(v_l_473_, 1);
lean_dec(v_unused_735_);
v_unused_736_ = lean_ctor_get(v_l_473_, 0);
lean_dec(v_unused_736_);
v___x_726_ = v_l_473_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_dec(v_l_473_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 4, v_r_663_);
lean_ctor_set(v___x_726_, 3, v___x_724_);
lean_ctor_set(v___x_726_, 2, v_v_661_);
lean_ctor_set(v___x_726_, 1, v_k_660_);
lean_ctor_set(v___x_726_, 0, v___x_721_);
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_k_660_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_v_661_);
lean_ctor_set(v_reuseFailAlloc_730_, 3, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_730_, 4, v_r_663_);
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
lean_dec_ref_known(v_l_662_, 5);
lean_del_object(v___x_674_);
lean_dec(v_v_661_);
lean_dec(v_k_660_);
lean_dec(v_size_659_);
lean_dec_ref_known(v_l_473_, 5);
lean_del_object(v___x_476_);
lean_dec(v_v_472_);
lean_dec(v_k_471_);
v___x_738_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7);
v___x_739_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v___x_738_);
return v___x_739_;
}
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; 
lean_del_object(v___x_674_);
lean_dec(v_r_663_);
lean_dec(v_v_661_);
lean_dec(v_k_660_);
lean_dec(v_size_659_);
lean_dec_ref_known(v_l_473_, 5);
lean_del_object(v___x_476_);
lean_dec(v_v_472_);
lean_dec(v_k_471_);
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
v_size_748_ = lean_ctor_get(v_l_473_, 0);
v___x_749_ = lean_unsigned_to_nat(1u);
v___x_750_ = lean_nat_add(v___x_749_, v_size_748_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_657_);
lean_ctor_set(v___x_476_, 0, v___x_750_);
v___x_752_ = v___x_476_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_753_, 3, v_l_473_);
lean_ctor_set(v_reuseFailAlloc_753_, 4, v___x_657_);
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
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_l_754_; 
v_l_754_ = lean_ctor_get(v___x_657_, 3);
lean_inc(v_l_754_);
if (lean_obj_tag(v_l_754_) == 0)
{
lean_object* v_r_755_; 
v_r_755_ = lean_ctor_get(v___x_657_, 4);
lean_inc(v_r_755_);
if (lean_obj_tag(v_r_755_) == 0)
{
lean_object* v_size_756_; lean_object* v_k_757_; lean_object* v_v_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_772_; 
v_size_756_ = lean_ctor_get(v___x_657_, 0);
v_k_757_ = lean_ctor_get(v___x_657_, 1);
v_v_758_ = lean_ctor_get(v___x_657_, 2);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_772_ == 0)
{
lean_object* v_unused_773_; lean_object* v_unused_774_; 
v_unused_773_ = lean_ctor_get(v___x_657_, 4);
lean_dec(v_unused_773_);
v_unused_774_ = lean_ctor_get(v___x_657_, 3);
lean_dec(v_unused_774_);
v___x_760_ = v___x_657_;
v_isShared_761_ = v_isSharedCheck_772_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_v_758_);
lean_inc(v_k_757_);
lean_inc(v_size_756_);
lean_dec(v___x_657_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_772_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v_size_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_767_; 
v_size_762_ = lean_ctor_get(v_l_754_, 0);
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = lean_nat_add(v___x_763_, v_size_756_);
lean_dec(v_size_756_);
v___x_765_ = lean_nat_add(v___x_763_, v_size_762_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 4, v_l_754_);
lean_ctor_set(v___x_760_, 3, v_l_473_);
lean_ctor_set(v___x_760_, 2, v_v_472_);
lean_ctor_set(v___x_760_, 1, v_k_471_);
lean_ctor_set(v___x_760_, 0, v___x_765_);
v___x_767_ = v___x_760_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_771_, 3, v_l_473_);
lean_ctor_set(v_reuseFailAlloc_771_, 4, v_l_754_);
v___x_767_ = v_reuseFailAlloc_771_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v_r_755_);
lean_ctor_set(v___x_476_, 3, v___x_767_);
lean_ctor_set(v___x_476_, 2, v_v_758_);
lean_ctor_set(v___x_476_, 1, v_k_757_);
lean_ctor_set(v___x_476_, 0, v___x_764_);
v___x_769_ = v___x_476_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_k_757_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_v_758_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_770_, 4, v_r_755_);
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
lean_object* v_k_775_; lean_object* v_v_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_800_; 
v_k_775_ = lean_ctor_get(v___x_657_, 1);
v_v_776_ = lean_ctor_get(v___x_657_, 2);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; lean_object* v_unused_802_; lean_object* v_unused_803_; 
v_unused_801_ = lean_ctor_get(v___x_657_, 4);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v___x_657_, 3);
lean_dec(v_unused_802_);
v_unused_803_ = lean_ctor_get(v___x_657_, 0);
lean_dec(v_unused_803_);
v___x_778_ = v___x_657_;
v_isShared_779_ = v_isSharedCheck_800_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_v_776_);
lean_inc(v_k_775_);
lean_dec(v___x_657_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_800_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v_k_780_; lean_object* v_v_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_796_; 
v_k_780_ = lean_ctor_get(v_l_754_, 1);
v_v_781_ = lean_ctor_get(v_l_754_, 2);
v_isSharedCheck_796_ = !lean_is_exclusive(v_l_754_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; lean_object* v_unused_798_; lean_object* v_unused_799_; 
v_unused_797_ = lean_ctor_get(v_l_754_, 4);
lean_dec(v_unused_797_);
v_unused_798_ = lean_ctor_get(v_l_754_, 3);
lean_dec(v_unused_798_);
v_unused_799_ = lean_ctor_get(v_l_754_, 0);
lean_dec(v_unused_799_);
v___x_783_ = v_l_754_;
v_isShared_784_ = v_isSharedCheck_796_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_v_781_);
lean_inc(v_k_780_);
lean_dec(v_l_754_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_796_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_785_ = lean_unsigned_to_nat(3u);
v___x_786_ = lean_unsigned_to_nat(1u);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 4, v_r_755_);
lean_ctor_set(v___x_783_, 3, v_r_755_);
lean_ctor_set(v___x_783_, 2, v_v_472_);
lean_ctor_set(v___x_783_, 1, v_k_471_);
lean_ctor_set(v___x_783_, 0, v___x_786_);
v___x_788_ = v___x_783_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_795_, 3, v_r_755_);
lean_ctor_set(v_reuseFailAlloc_795_, 4, v_r_755_);
v___x_788_ = v_reuseFailAlloc_795_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_790_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 3, v_r_755_);
lean_ctor_set(v___x_778_, 0, v___x_786_);
v___x_790_ = v___x_778_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_k_775_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v_v_776_);
lean_ctor_set(v_reuseFailAlloc_794_, 3, v_r_755_);
lean_ctor_set(v_reuseFailAlloc_794_, 4, v_r_755_);
v___x_790_ = v_reuseFailAlloc_794_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_792_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_790_);
lean_ctor_set(v___x_476_, 3, v___x_788_);
lean_ctor_set(v___x_476_, 2, v_v_781_);
lean_ctor_set(v___x_476_, 1, v_k_780_);
lean_ctor_set(v___x_476_, 0, v___x_785_);
v___x_792_ = v___x_476_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_k_780_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v_v_781_);
lean_ctor_set(v_reuseFailAlloc_793_, 3, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_793_, 4, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_804_; 
v_r_804_ = lean_ctor_get(v___x_657_, 4);
lean_inc(v_r_804_);
if (lean_obj_tag(v_r_804_) == 0)
{
lean_object* v_k_805_; lean_object* v_v_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_818_; 
v_k_805_ = lean_ctor_get(v___x_657_, 1);
v_v_806_ = lean_ctor_get(v___x_657_, 2);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; lean_object* v_unused_820_; lean_object* v_unused_821_; 
v_unused_819_ = lean_ctor_get(v___x_657_, 4);
lean_dec(v_unused_819_);
v_unused_820_ = lean_ctor_get(v___x_657_, 3);
lean_dec(v_unused_820_);
v_unused_821_ = lean_ctor_get(v___x_657_, 0);
lean_dec(v_unused_821_);
v___x_808_ = v___x_657_;
v_isShared_809_ = v_isSharedCheck_818_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_v_806_);
lean_inc(v_k_805_);
lean_dec(v___x_657_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_818_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_810_ = lean_unsigned_to_nat(3u);
v___x_811_ = lean_unsigned_to_nat(1u);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 4, v_l_754_);
lean_ctor_set(v___x_808_, 2, v_v_472_);
lean_ctor_set(v___x_808_, 1, v_k_471_);
lean_ctor_set(v___x_808_, 0, v___x_811_);
v___x_813_ = v___x_808_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_817_, 3, v_l_754_);
lean_ctor_set(v_reuseFailAlloc_817_, 4, v_l_754_);
v___x_813_ = v_reuseFailAlloc_817_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_815_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v_r_804_);
lean_ctor_set(v___x_476_, 3, v___x_813_);
lean_ctor_set(v___x_476_, 2, v_v_806_);
lean_ctor_set(v___x_476_, 1, v_k_805_);
lean_ctor_set(v___x_476_, 0, v___x_810_);
v___x_815_ = v___x_476_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_k_805_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_v_806_);
lean_ctor_set(v_reuseFailAlloc_816_, 3, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_816_, 4, v_r_804_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
else
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = lean_unsigned_to_nat(2u);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_657_);
lean_ctor_set(v___x_476_, 3, v_r_804_);
lean_ctor_set(v___x_476_, 0, v___x_822_);
v___x_824_ = v___x_476_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_825_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_825_, 3, v_r_804_);
lean_ctor_set(v_reuseFailAlloc_825_, 4, v___x_657_);
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
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_657_);
lean_ctor_set(v___x_476_, 3, v___x_657_);
lean_ctor_set(v___x_476_, 0, v___x_826_);
v___x_828_ = v___x_476_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_829_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_829_, 3, v___x_657_);
lean_ctor_set(v_reuseFailAlloc_829_, 4, v___x_657_);
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
}
else
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_unsigned_to_nat(1u);
v___x_832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v_k_467_);
lean_ctor_set(v___x_832_, 2, v_v_468_);
lean_ctor_set(v___x_832_, 3, v_t_469_);
lean_ctor_set(v___x_832_, 4, v_t_469_);
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
lean_dec_ref_known(v_x_834_, 5);
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
lean_dec_ref_known(v_x_849_, 3);
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
lean_dec_ref_known(v___x_874_, 2);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_854_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
lean_ctor_set(v___x_877_, 1, v___x_870_);
v___x_878_ = l_Lean_Json_mkObj(v___x_877_);
lean_dec_ref_known(v___x_877_, 2);
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
lean_dec_ref_known(v_x_849_, 6);
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
lean_dec_ref_known(v___x_917_, 2);
v___x_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_886_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
lean_ctor_set(v___x_920_, 1, v___x_910_);
v___x_921_ = l_Lean_Json_mkObj(v___x_920_);
lean_dec_ref_known(v___x_920_, 2);
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
lean_dec_ref_known(v_t_947_, 1);
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
lean_dec_ref_known(v_t_947_, 4);
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
static lean_object* _init_l_Lake_instInhabitedPackageEntry_default___closed__0(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_988_ = ((lean_object*)(l_Lake_instInhabitedPackageEntrySrc_default));
v___x_989_ = lean_box(0);
v___x_990_ = l_Lake_defaultConfigFile;
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
LEAN_EXPORT lean_object* l_Lake_PackageEntry_prettyName(lean_object* v_entry_997_){
_start:
{
lean_object* v_name_998_; uint8_t v___x_999_; lean_object* v___x_1000_; 
v_name_998_ = lean_ctor_get(v_entry_997_, 0);
lean_inc(v_name_998_);
lean_dec_ref(v_entry_997_);
v___x_999_ = 0;
v___x_1000_ = l_Lean_Name_toString(v_name_998_, v___x_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_toJson(lean_object* v_entry_1017_){
_start:
{
lean_object* v_name_1018_; lean_object* v_scope_1019_; uint8_t v_inherited_1020_; lean_object* v_configFile_1021_; lean_object* v_manifestFile_x3f_1022_; lean_object* v_src_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v_fields_1047_; 
v_name_1018_ = lean_ctor_get(v_entry_1017_, 0);
lean_inc(v_name_1018_);
v_scope_1019_ = lean_ctor_get(v_entry_1017_, 1);
lean_inc_ref(v_scope_1019_);
v_inherited_1020_ = lean_ctor_get_uint8(v_entry_1017_, sizeof(void*)*5);
v_configFile_1021_ = lean_ctor_get(v_entry_1017_, 2);
lean_inc_ref(v_configFile_1021_);
v_manifestFile_x3f_1022_ = lean_ctor_get(v_entry_1017_, 3);
lean_inc(v_manifestFile_x3f_1022_);
v_src_1023_ = lean_ctor_get(v_entry_1017_, 4);
lean_inc_ref(v_src_1023_);
lean_dec_ref(v_entry_1017_);
v___x_1024_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_1025_ = 1;
v___x_1026_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1018_, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1024_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__0));
v___x_1030_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1030_, 0, v_scope_1019_);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__1));
v___x_1033_ = l_Lake_mkRelPathString(v_configFile_1021_);
v___x_1034_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
v___x_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1032_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__2));
v___x_1037_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_manifestFile_x3f_1022_);
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10));
v___x_1040_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1040_, 0, v_inherited_1020_);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1039_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = lean_box(0);
v___x_1043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1041_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1038_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1035_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1031_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v_fields_1047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_fields_1047_, 0, v___x_1028_);
lean_ctor_set(v_fields_1047_, 1, v___x_1046_);
if (lean_obj_tag(v_src_1023_) == 0)
{
lean_object* v_dir_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1063_; 
v_dir_1048_ = lean_ctor_get(v_src_1023_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_src_1023_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1050_ = v_src_1023_;
v_isShared_1051_ = v_isSharedCheck_1063_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_dir_1048_);
lean_dec(v_src_1023_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1063_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1052_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__5));
v___x_1053_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22));
v___x_1054_ = l_Lake_mkRelPathString(v_dir_1048_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set_tag(v___x_1050_, 3);
lean_ctor_set(v___x_1050_, 0, v___x_1054_);
v___x_1056_ = v___x_1050_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1053_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v___x_1042_);
v___x_1059_ = l_List_appendTR___redArg(v_fields_1047_, v___x_1058_);
v___x_1060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1052_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = l_Lean_Json_mkObj(v___x_1060_);
lean_dec_ref_known(v___x_1060_, 2);
return v___x_1061_;
}
}
}
else
{
lean_object* v_url_1064_; lean_object* v_rev_1065_; lean_object* v_inputRev_x3f_1066_; lean_object* v_subDir_x3f_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v_url_1064_ = lean_ctor_get(v_src_1023_, 0);
lean_inc_ref(v_url_1064_);
v_rev_1065_ = lean_ctor_get(v_src_1023_, 1);
lean_inc_ref(v_rev_1065_);
v_inputRev_x3f_1066_ = lean_ctor_get(v_src_1023_, 2);
lean_inc(v_inputRev_x3f_1066_);
v_subDir_x3f_1067_ = lean_ctor_get(v_src_1023_, 3);
lean_inc(v_subDir_x3f_1067_);
lean_dec_ref_known(v_src_1023_, 4);
v___x_1068_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__7));
v___x_1069_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12));
v___x_1070_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1070_, 0, v_url_1064_);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14));
v___x_1073_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1073_, 0, v_rev_1065_);
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__8));
v___x_1076_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__1(v_inputRev_x3f_1066_);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__9));
v___x_1079_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_subDir_x3f_1067_);
v___x_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set(v___x_1081_, 1, v___x_1042_);
v___x_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1077_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1074_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1071_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = l_List_appendTR___redArg(v_fields_1047_, v___x_1084_);
v___x_1086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1068_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = l_Lean_Json_mkObj(v___x_1086_);
lean_dec_ref_known(v___x_1086_, 2);
return v___x_1087_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0(lean_object* v_x_1091_){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0));
v___x_1093_ = lean_string_append(v___x_1092_, v_x_1091_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0___boxed(lean_object* v_x_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_x_1094_);
lean_dec_ref(v_x_1094_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f(lean_object* v_json_1116_){
_start:
{
lean_object* v_a_1118_; lean_object* v___x_1121_; 
v___x_1121_ = l_Lean_Json_getObj_x3f(v_json_1116_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1130_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1124_ = v___x_1121_;
v_isShared_1125_ = v_isSharedCheck_1130_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1121_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1130_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; lean_object* v___x_1128_; 
v___x_1126_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_a_1122_);
lean_dec(v_a_1122_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1126_);
v___x_1128_ = v___x_1124_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
else
{
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
v_a_1131_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1121_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1121_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 0);
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1361_; 
v_a_1139_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1141_ = v___x_1121_;
v_isShared_1142_ = v_isSharedCheck_1361_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1121_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1361_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_1144_ = l_Lake_JsonObject_getJson_x3f(v_a_1139_, v___x_1143_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v___x_1145_; 
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v___x_1145_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__0));
v_a_1118_ = v___x_1145_;
goto v___jp_1117_;
}
else
{
lean_object* v_val_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1360_; 
v_val_1146_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1148_ = v___x_1144_;
v_isShared_1149_ = v_isSharedCheck_1360_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_val_1146_);
lean_dec(v___x_1144_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1360_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_Name_fromJson_x3f(v_val_1146_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
lean_dec_ref_known(v___x_1150_, 1);
v___x_1152_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__1));
v___x_1153_ = lean_string_append(v___x_1152_, v_a_1151_);
lean_dec(v_a_1151_);
v_a_1118_ = v___x_1153_;
goto v___jp_1117_;
}
else
{
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1154_; 
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v_a_1154_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1154_);
lean_dec_ref_known(v___x_1150_, 1);
v_a_1118_ = v_a_1154_;
goto v___jp_1117_;
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1359_; 
v_a_1155_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1157_ = v___x_1150_;
v_isShared_1158_ = v_isSharedCheck_1359_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1150_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1359_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v_a_1160_; lean_object* v___y_1172_; lean_object* v___y_1173_; uint8_t v___y_1174_; lean_object* v___y_1175_; lean_object* v_a_1176_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; uint8_t v___y_1190_; lean_object* v___y_1191_; lean_object* v_a_1192_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; uint8_t v___y_1199_; lean_object* v___y_1200_; lean_object* v_a_1201_; lean_object* v___y_1213_; uint8_t v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v_a_1217_; lean_object* v___y_1273_; uint8_t v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1279_; uint8_t v___y_1280_; lean_object* v___y_1281_; lean_object* v_a_1282_; lean_object* v___y_1294_; uint8_t v___y_1295_; lean_object* v___y_1296_; lean_object* v_a_1299_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__0));
v___x_1336_ = l_Lake_JsonObject_getJson_x3f(v_a_1139_, v___x_1335_);
if (lean_obj_tag(v___x_1336_) == 0)
{
goto v___jp_1333_;
}
else
{
lean_object* v_val_1337_; lean_object* v___x_1338_; 
v_val_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_val_1337_);
lean_dec_ref_known(v___x_1336_, 1);
v___x_1338_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(v_val_1337_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1348_; 
lean_del_object(v___x_1157_);
lean_dec(v_a_1155_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1341_ = v___x_1338_;
v_isShared_1342_ = v_isSharedCheck_1348_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1338_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1348_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
v___x_1343_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__19));
v___x_1344_ = lean_string_append(v___x_1343_, v_a_1339_);
lean_dec(v_a_1339_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v___x_1344_);
v___x_1346_ = v___x_1341_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
else
{
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_del_object(v___x_1157_);
lean_dec(v_a_1155_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v_a_1349_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1338_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1338_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
lean_ctor_set_tag(v___x_1351_, 0);
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
lean_object* v_a_1357_; 
v_a_1357_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_a_1357_);
lean_dec_ref_known(v___x_1338_, 1);
if (lean_obj_tag(v_a_1357_) == 0)
{
goto v___jp_1333_;
}
else
{
lean_object* v_val_1358_; 
v_val_1358_ = lean_ctor_get(v_a_1357_, 0);
lean_inc(v_val_1358_);
lean_dec_ref_known(v_a_1357_, 1);
v_a_1299_ = v_val_1358_;
goto v___jp_1298_;
}
}
}
}
v___jp_1159_:
{
lean_object* v___x_1161_; uint8_t v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1161_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__2));
v___x_1162_ = 1;
v___x_1163_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_1155_, v___x_1162_);
v___x_1164_ = lean_string_append(v___x_1161_, v___x_1163_);
lean_dec_ref(v___x_1163_);
v___x_1165_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__3));
v___x_1166_ = lean_string_append(v___x_1164_, v___x_1165_);
v___x_1167_ = lean_string_append(v___x_1166_, v_a_1160_);
lean_dec_ref(v_a_1160_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set_tag(v___x_1157_, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1167_);
v___x_1169_ = v___x_1157_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
v___jp_1171_:
{
lean_object* v___x_1178_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___y_1172_);
v___x_1178_ = v___x_1148_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___y_1172_);
v___x_1178_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1179_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1179_, 0, v_a_1155_);
lean_ctor_set(v___x_1179_, 1, v___y_1173_);
lean_ctor_set(v___x_1179_, 2, v___y_1175_);
lean_ctor_set(v___x_1179_, 3, v___x_1178_);
lean_ctor_set(v___x_1179_, 4, v_a_1176_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*5, v___y_1174_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1179_);
v___x_1181_ = v___x_1141_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
v___jp_1184_:
{
lean_object* v___x_1193_; 
v___x_1193_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1193_, 0, v___y_1189_);
lean_ctor_set(v___x_1193_, 1, v___y_1188_);
lean_ctor_set(v___x_1193_, 2, v___y_1187_);
lean_ctor_set(v___x_1193_, 3, v_a_1192_);
v___y_1172_ = v___y_1185_;
v___y_1173_ = v___y_1186_;
v___y_1174_ = v___y_1190_;
v___y_1175_ = v___y_1191_;
v_a_1176_ = v___x_1193_;
goto v___jp_1171_;
}
v___jp_1194_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__9));
v___x_1203_ = l_Lake_JsonObject_getJson_x3f(v_a_1139_, v___x_1202_);
lean_dec(v_a_1139_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v___x_1204_; 
lean_del_object(v___x_1157_);
v___x_1204_ = lean_box(0);
v___y_1185_ = v___y_1195_;
v___y_1186_ = v___y_1196_;
v___y_1187_ = v_a_1201_;
v___y_1188_ = v___y_1198_;
v___y_1189_ = v___y_1197_;
v___y_1190_ = v___y_1199_;
v___y_1191_ = v___y_1200_;
v_a_1192_ = v___x_1204_;
goto v___jp_1184_;
}
else
{
lean_object* v_val_1205_; lean_object* v___x_1206_; 
v_val_1205_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_val_1205_);
lean_dec_ref_known(v___x_1203_, 1);
v___x_1206_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1205_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec(v_a_1201_);
lean_dec_ref(v___y_1200_);
lean_dec_ref(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1207_);
lean_dec_ref_known(v___x_1206_, 1);
v___x_1208_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__4));
v___x_1209_ = lean_string_append(v___x_1208_, v_a_1207_);
lean_dec(v_a_1207_);
v_a_1160_ = v___x_1209_;
goto v___jp_1159_;
}
else
{
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1210_; 
lean_dec(v_a_1201_);
lean_dec_ref(v___y_1200_);
lean_dec_ref(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
v_a_1210_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1210_);
lean_dec_ref_known(v___x_1206_, 1);
v_a_1160_ = v_a_1210_;
goto v___jp_1159_;
}
else
{
lean_object* v_a_1211_; 
lean_del_object(v___x_1157_);
v_a_1211_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1211_);
lean_dec_ref_known(v___x_1206_, 1);
v___y_1185_ = v___y_1195_;
v___y_1186_ = v___y_1196_;
v___y_1187_ = v_a_1201_;
v___y_1188_ = v___y_1198_;
v___y_1189_ = v___y_1197_;
v___y_1190_ = v___y_1199_;
v___y_1191_ = v___y_1200_;
v_a_1192_ = v_a_1211_;
goto v___jp_1184_;
}
}
}
}
v___jp_1212_:
{
lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1218_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2));
v___x_1219_ = lean_string_dec_eq(v___y_1216_, v___x_1218_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1220_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3));
v___x_1221_ = lean_string_dec_eq(v___y_1216_, v___x_1220_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
lean_dec_ref(v_a_1217_);
lean_dec_ref(v___y_1215_);
lean_dec_ref(v___y_1213_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v___x_1222_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__5));
v___x_1223_ = lean_string_append(v___x_1222_, v___y_1216_);
lean_dec_ref(v___y_1216_);
v___x_1224_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1225_ = lean_string_append(v___x_1223_, v___x_1224_);
v_a_1160_ = v___x_1225_;
goto v___jp_1159_;
}
else
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
lean_dec_ref(v___y_1216_);
v___x_1226_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12));
v___x_1227_ = l_Lake_JsonObject_getJson_x3f(v_a_1139_, v___x_1226_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v___x_1228_; 
lean_dec_ref(v_a_1217_);
lean_dec_ref(v___y_1215_);
lean_dec_ref(v___y_1213_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v___x_1228_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__6));
v_a_1160_ = v___x_1228_;
goto v___jp_1159_;
}
else
{
lean_object* v_val_1229_; lean_object* v___x_1230_; 
v_val_1229_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_val_1229_);
lean_dec_ref_known(v___x_1227_, 1);
v___x_1230_ = l_Lean_Json_getStr_x3f(v_val_1229_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_dec_ref(v_a_1217_);
lean_dec_ref(v___y_1215_);
lean_dec_ref(v___y_1213_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1231_);
lean_dec_ref_known(v___x_1230_, 1);
v___x_1232_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__7));
v___x_1233_ = lean_string_append(v___x_1232_, v_a_1231_);
lean_dec(v_a_1231_);
v_a_1160_ = v___x_1233_;
goto v___jp_1159_;
}
else
{
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1234_; 
lean_dec_ref(v_a_1217_);
lean_dec_ref(v___y_1215_);
lean_dec_ref(v___y_1213_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v_a_1234_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1234_);
lean_dec_ref_known(v___x_1230_, 1);
v_a_1160_ = v_a_1234_;
goto v___jp_1159_;
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v_a_1235_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1230_, 1);
v___x_1236_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14));
v___x_1237_ = l_Lake_JsonObject_getJson_x3f(v_a_1139_, v___x_1236_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v___x_1238_; 
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1217_);
lean_dec_ref(v___y_1215_);
lean_dec_ref(v___y_1213_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v___x_1238_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__8));
v_a_1160_ = v___x_1238_;
goto v___jp_1159_;
}
else
{
lean_object* v_val_1239_; lean_object* v___x_1240_; 
v_val_1239_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_val_1239_);
lean_dec_ref_known(v___x_1237_, 1);
v___x_1240_ = l_Lean_Json_getStr_x3f(v_val_1239_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1217_);
lean_dec_ref(v___y_1215_);
lean_dec_ref(v___y_1213_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref_known(v___x_1240_, 1);
v___x_1242_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__9));
v___x_1243_ = lean_string_append(v___x_1242_, v_a_1241_);
lean_dec(v_a_1241_);
v_a_1160_ = v___x_1243_;
goto v___jp_1159_;
}
else
{
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1244_; 
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1217_);
lean_dec_ref(v___y_1215_);
lean_dec_ref(v___y_1213_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v_a_1244_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1244_);
lean_dec_ref_known(v___x_1240_, 1);
v_a_1160_ = v_a_1244_;
goto v___jp_1159_;
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v_a_1245_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1240_, 1);
v___x_1246_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__8));
v___x_1247_ = l_Lake_JsonObject_getJson_x3f(v_a_1139_, v___x_1246_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_box(0);
v___y_1195_ = v_a_1217_;
v___y_1196_ = v___y_1213_;
v___y_1197_ = v_a_1235_;
v___y_1198_ = v_a_1245_;
v___y_1199_ = v___y_1214_;
v___y_1200_ = v___y_1215_;
v_a_1201_ = v___x_1248_;
goto v___jp_1194_;
}
else
{
lean_object* v_val_1249_; lean_object* v___x_1250_; 
v_val_1249_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_val_1249_);
lean_dec_ref_known(v___x_1247_, 1);
v___x_1250_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(v_val_1249_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_dec(v_a_1245_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1217_);
lean_dec_ref(v___y_1215_);
lean_dec_ref(v___y_1213_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1251_);
lean_dec_ref_known(v___x_1250_, 1);
v___x_1252_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__10));
v___x_1253_ = lean_string_append(v___x_1252_, v_a_1251_);
lean_dec(v_a_1251_);
v_a_1160_ = v___x_1253_;
goto v___jp_1159_;
}
else
{
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1254_; 
lean_dec(v_a_1245_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1217_);
lean_dec_ref(v___y_1215_);
lean_dec_ref(v___y_1213_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v_a_1254_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___x_1250_, 1);
v_a_1160_ = v_a_1254_;
goto v___jp_1159_;
}
else
{
lean_object* v_a_1255_; 
v_a_1255_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___x_1250_, 1);
v___y_1195_ = v_a_1217_;
v___y_1196_ = v___y_1213_;
v___y_1197_ = v_a_1235_;
v___y_1198_ = v_a_1245_;
v___y_1199_ = v___y_1214_;
v___y_1200_ = v___y_1215_;
v_a_1201_ = v_a_1255_;
goto v___jp_1194_;
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
lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_dec_ref(v___y_1216_);
v___x_1256_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22));
v___x_1257_ = l_Lake_JsonObject_getJson_x3f(v_a_1139_, v___x_1256_);
lean_dec(v_a_1139_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v___x_1258_; 
lean_dec_ref(v_a_1217_);
lean_dec_ref(v___y_1215_);
lean_dec_ref(v___y_1213_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
v___x_1258_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__11));
v_a_1160_ = v___x_1258_;
goto v___jp_1159_;
}
else
{
lean_object* v_val_1259_; lean_object* v___x_1260_; 
v_val_1259_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_val_1259_);
lean_dec_ref_known(v___x_1257_, 1);
v___x_1260_ = l_Lean_Json_getStr_x3f(v_val_1259_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
lean_dec_ref(v_a_1217_);
lean_dec_ref(v___y_1215_);
lean_dec_ref(v___y_1213_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___x_1260_, 1);
v___x_1262_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__12));
v___x_1263_ = lean_string_append(v___x_1262_, v_a_1261_);
lean_dec(v_a_1261_);
v_a_1160_ = v___x_1263_;
goto v___jp_1159_;
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_del_object(v___x_1157_);
v_a_1264_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1260_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1260_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set_tag(v___x_1266_, 0);
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
v___y_1172_ = v_a_1217_;
v___y_1173_ = v___y_1213_;
v___y_1174_ = v___y_1214_;
v___y_1175_ = v___y_1215_;
v_a_1176_ = v___x_1269_;
goto v___jp_1171_;
}
}
}
}
}
}
v___jp_1272_:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lake_defaultManifestFile;
v___y_1213_ = v___y_1273_;
v___y_1214_ = v___y_1274_;
v___y_1215_ = v___y_1275_;
v___y_1216_ = v___y_1276_;
v_a_1217_ = v___x_1277_;
goto v___jp_1212_;
}
v___jp_1278_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__2));
v___x_1284_ = l_Lake_JsonObject_getJson_x3f(v_a_1139_, v___x_1283_);
if (lean_obj_tag(v___x_1284_) == 0)
{
v___y_1273_ = v___y_1279_;
v___y_1274_ = v___y_1280_;
v___y_1275_ = v_a_1282_;
v___y_1276_ = v___y_1281_;
goto v___jp_1272_;
}
else
{
lean_object* v_val_1285_; lean_object* v___x_1286_; 
v_val_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_val_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1286_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1285_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_dec_ref(v_a_1282_);
lean_dec_ref(v___y_1281_);
lean_dec_ref(v___y_1279_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1286_, 1);
v___x_1288_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__13));
v___x_1289_ = lean_string_append(v___x_1288_, v_a_1287_);
lean_dec(v_a_1287_);
v_a_1160_ = v___x_1289_;
goto v___jp_1159_;
}
else
{
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1290_; 
lean_dec_ref(v_a_1282_);
lean_dec_ref(v___y_1281_);
lean_dec_ref(v___y_1279_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v_a_1290_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1290_);
lean_dec_ref_known(v___x_1286_, 1);
v_a_1160_ = v_a_1290_;
goto v___jp_1159_;
}
else
{
lean_object* v_a_1291_; 
v_a_1291_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1291_);
lean_dec_ref_known(v___x_1286_, 1);
if (lean_obj_tag(v_a_1291_) == 0)
{
v___y_1273_ = v___y_1279_;
v___y_1274_ = v___y_1280_;
v___y_1275_ = v_a_1282_;
v___y_1276_ = v___y_1281_;
goto v___jp_1272_;
}
else
{
lean_object* v_val_1292_; 
v_val_1292_ = lean_ctor_get(v_a_1291_, 0);
lean_inc(v_val_1292_);
lean_dec_ref_known(v_a_1291_, 1);
v___y_1213_ = v___y_1279_;
v___y_1214_ = v___y_1280_;
v___y_1215_ = v_a_1282_;
v___y_1216_ = v___y_1281_;
v_a_1217_ = v_val_1292_;
goto v___jp_1212_;
}
}
}
}
}
v___jp_1293_:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lake_defaultConfigFile;
v___y_1279_ = v___y_1294_;
v___y_1280_ = v___y_1295_;
v___y_1281_ = v___y_1296_;
v_a_1282_ = v___x_1297_;
goto v___jp_1278_;
}
v___jp_1298_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__3));
v___x_1301_ = l_Lake_JsonObject_getJson_x3f(v_a_1139_, v___x_1300_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v___x_1302_; 
lean_dec_ref(v_a_1299_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v___x_1302_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__14));
v_a_1160_ = v___x_1302_;
goto v___jp_1159_;
}
else
{
lean_object* v_val_1303_; lean_object* v___x_1304_; 
v_val_1303_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_val_1303_);
lean_dec_ref_known(v___x_1301_, 1);
v___x_1304_ = l_Lean_Json_getStr_x3f(v_val_1303_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
lean_dec_ref(v_a_1299_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref_known(v___x_1304_, 1);
v___x_1306_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__15));
v___x_1307_ = lean_string_append(v___x_1306_, v_a_1305_);
lean_dec(v_a_1305_);
v_a_1160_ = v___x_1307_;
goto v___jp_1159_;
}
else
{
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1308_; 
lean_dec_ref(v_a_1299_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v_a_1308_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1308_);
lean_dec_ref_known(v___x_1304_, 1);
v_a_1160_ = v_a_1308_;
goto v___jp_1159_;
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v_a_1309_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1304_, 1);
v___x_1310_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10));
v___x_1311_ = l_Lake_JsonObject_getJson_x3f(v_a_1139_, v___x_1310_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v___x_1312_; 
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1299_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v___x_1312_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__16));
v_a_1160_ = v___x_1312_;
goto v___jp_1159_;
}
else
{
lean_object* v_val_1313_; lean_object* v___x_1314_; 
v_val_1313_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_val_1313_);
lean_dec_ref_known(v___x_1311_, 1);
v___x_1314_ = l_Lean_Json_getBool_x3f(v_val_1313_);
lean_dec(v_val_1313_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1299_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1315_);
lean_dec_ref_known(v___x_1314_, 1);
v___x_1316_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__17));
v___x_1317_ = lean_string_append(v___x_1316_, v_a_1315_);
lean_dec(v_a_1315_);
v_a_1160_ = v___x_1317_;
goto v___jp_1159_;
}
else
{
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1318_; 
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1299_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v_a_1318_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1314_, 1);
v_a_1160_ = v_a_1318_;
goto v___jp_1159_;
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v_a_1319_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1314_, 1);
v___x_1320_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__1));
v___x_1321_ = l_Lake_JsonObject_getJson_x3f(v_a_1139_, v___x_1320_);
if (lean_obj_tag(v___x_1321_) == 0)
{
uint8_t v___x_1322_; 
v___x_1322_ = lean_unbox(v_a_1319_);
lean_dec(v_a_1319_);
v___y_1294_ = v_a_1299_;
v___y_1295_ = v___x_1322_;
v___y_1296_ = v_a_1309_;
goto v___jp_1293_;
}
else
{
lean_object* v_val_1323_; lean_object* v___x_1324_; 
v_val_1323_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_val_1323_);
lean_dec_ref_known(v___x_1321_, 1);
v___x_1324_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1323_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
lean_dec(v_a_1319_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1299_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1324_, 1);
v___x_1326_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__18));
v___x_1327_ = lean_string_append(v___x_1326_, v_a_1325_);
lean_dec(v_a_1325_);
v_a_1160_ = v___x_1327_;
goto v___jp_1159_;
}
else
{
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1328_; 
lean_dec(v_a_1319_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1299_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1139_);
v_a_1328_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1324_, 1);
v_a_1160_ = v_a_1328_;
goto v___jp_1159_;
}
else
{
lean_object* v_a_1329_; 
v_a_1329_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v___x_1324_, 1);
if (lean_obj_tag(v_a_1329_) == 0)
{
uint8_t v___x_1330_; 
v___x_1330_ = lean_unbox(v_a_1319_);
lean_dec(v_a_1319_);
v___y_1294_ = v_a_1299_;
v___y_1295_ = v___x_1330_;
v___y_1296_ = v_a_1309_;
goto v___jp_1293_;
}
else
{
lean_object* v_val_1331_; uint8_t v___x_1332_; 
v_val_1331_ = lean_ctor_get(v_a_1329_, 0);
lean_inc(v_val_1331_);
lean_dec_ref_known(v_a_1329_, 1);
v___x_1332_ = lean_unbox(v_a_1319_);
lean_dec(v_a_1319_);
v___y_1279_ = v_a_1299_;
v___y_1280_ = v___x_1332_;
v___y_1281_ = v_a_1309_;
v_a_1282_ = v_val_1331_;
goto v___jp_1278_;
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
v___jp_1333_:
{
lean_object* v___x_1334_; 
v___x_1334_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v_a_1299_ = v___x_1334_;
goto v___jp_1298_;
}
}
}
}
}
}
}
}
}
v___jp_1117_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_a_1118_);
lean_dec_ref(v_a_1118_);
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
return v___x_1120_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setInherited(lean_object* v_entry_1364_){
_start:
{
lean_object* v_name_1365_; lean_object* v_scope_1366_; lean_object* v_configFile_1367_; lean_object* v_manifestFile_x3f_1368_; lean_object* v_src_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1377_; 
v_name_1365_ = lean_ctor_get(v_entry_1364_, 0);
v_scope_1366_ = lean_ctor_get(v_entry_1364_, 1);
v_configFile_1367_ = lean_ctor_get(v_entry_1364_, 2);
v_manifestFile_x3f_1368_ = lean_ctor_get(v_entry_1364_, 3);
v_src_1369_ = lean_ctor_get(v_entry_1364_, 4);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_entry_1364_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1371_ = v_entry_1364_;
v_isShared_1372_ = v_isSharedCheck_1377_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_src_1369_);
lean_inc(v_manifestFile_x3f_1368_);
lean_inc(v_configFile_1367_);
lean_inc(v_scope_1366_);
lean_inc(v_name_1365_);
lean_dec(v_entry_1364_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1377_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
uint8_t v___x_1373_; lean_object* v___x_1375_; 
v___x_1373_ = 1;
if (v_isShared_1372_ == 0)
{
v___x_1375_ = v___x_1371_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_name_1365_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_scope_1366_);
lean_ctor_set(v_reuseFailAlloc_1376_, 2, v_configFile_1367_);
lean_ctor_set(v_reuseFailAlloc_1376_, 3, v_manifestFile_x3f_1368_);
lean_ctor_set(v_reuseFailAlloc_1376_, 4, v_src_1369_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_ctor_set_uint8(v___x_1375_, sizeof(void*)*5, v___x_1373_);
return v___x_1375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setConfigFile(lean_object* v_path_1378_, lean_object* v_entry_1379_){
_start:
{
lean_object* v_name_1380_; lean_object* v_scope_1381_; uint8_t v_inherited_1382_; lean_object* v_manifestFile_x3f_1383_; lean_object* v_src_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
v_name_1380_ = lean_ctor_get(v_entry_1379_, 0);
v_scope_1381_ = lean_ctor_get(v_entry_1379_, 1);
v_inherited_1382_ = lean_ctor_get_uint8(v_entry_1379_, sizeof(void*)*5);
v_manifestFile_x3f_1383_ = lean_ctor_get(v_entry_1379_, 3);
v_src_1384_ = lean_ctor_get(v_entry_1379_, 4);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_entry_1379_);
if (v_isSharedCheck_1391_ == 0)
{
lean_object* v_unused_1392_; 
v_unused_1392_ = lean_ctor_get(v_entry_1379_, 2);
lean_dec(v_unused_1392_);
v___x_1386_ = v_entry_1379_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_src_1384_);
lean_inc(v_manifestFile_x3f_1383_);
lean_inc(v_scope_1381_);
lean_inc(v_name_1380_);
lean_dec(v_entry_1379_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 2, v_path_1378_);
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_name_1380_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_scope_1381_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v_path_1378_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v_manifestFile_x3f_1383_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v_src_1384_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, sizeof(void*)*5, v_inherited_1382_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setManifestFile(lean_object* v_path_x3f_1393_, lean_object* v_entry_1394_){
_start:
{
lean_object* v_name_1395_; lean_object* v_scope_1396_; uint8_t v_inherited_1397_; lean_object* v_configFile_1398_; lean_object* v_src_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
v_name_1395_ = lean_ctor_get(v_entry_1394_, 0);
v_scope_1396_ = lean_ctor_get(v_entry_1394_, 1);
v_inherited_1397_ = lean_ctor_get_uint8(v_entry_1394_, sizeof(void*)*5);
v_configFile_1398_ = lean_ctor_get(v_entry_1394_, 2);
v_src_1399_ = lean_ctor_get(v_entry_1394_, 4);
v_isSharedCheck_1406_ = !lean_is_exclusive(v_entry_1394_);
if (v_isSharedCheck_1406_ == 0)
{
lean_object* v_unused_1407_; 
v_unused_1407_ = lean_ctor_get(v_entry_1394_, 3);
lean_dec(v_unused_1407_);
v___x_1401_ = v_entry_1394_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_src_1399_);
lean_inc(v_configFile_1398_);
lean_inc(v_scope_1396_);
lean_inc(v_name_1395_);
lean_dec(v_entry_1394_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 3, v_path_x3f_1393_);
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_name_1395_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_scope_1396_);
lean_ctor_set(v_reuseFailAlloc_1405_, 2, v_configFile_1398_);
lean_ctor_set(v_reuseFailAlloc_1405_, 3, v_path_x3f_1393_);
lean_ctor_set(v_reuseFailAlloc_1405_, 4, v_src_1399_);
lean_ctor_set_uint8(v_reuseFailAlloc_1405_, sizeof(void*)*5, v_inherited_1397_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_inDirectory(lean_object* v_pkgDir_1408_, lean_object* v_entry_1409_){
_start:
{
lean_object* v_src_1410_; 
v_src_1410_ = lean_ctor_get(v_entry_1409_, 4);
lean_inc_ref(v_src_1410_);
if (lean_obj_tag(v_src_1410_) == 0)
{
lean_object* v_name_1411_; lean_object* v_scope_1412_; uint8_t v_inherited_1413_; lean_object* v_configFile_1414_; lean_object* v_manifestFile_x3f_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1431_; 
v_name_1411_ = lean_ctor_get(v_entry_1409_, 0);
v_scope_1412_ = lean_ctor_get(v_entry_1409_, 1);
v_inherited_1413_ = lean_ctor_get_uint8(v_entry_1409_, sizeof(void*)*5);
v_configFile_1414_ = lean_ctor_get(v_entry_1409_, 2);
v_manifestFile_x3f_1415_ = lean_ctor_get(v_entry_1409_, 3);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_entry_1409_);
if (v_isSharedCheck_1431_ == 0)
{
lean_object* v_unused_1432_; 
v_unused_1432_ = lean_ctor_get(v_entry_1409_, 4);
lean_dec(v_unused_1432_);
v___x_1417_ = v_entry_1409_;
v_isShared_1418_ = v_isSharedCheck_1431_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_manifestFile_x3f_1415_);
lean_inc(v_configFile_1414_);
lean_inc(v_scope_1412_);
lean_inc(v_name_1411_);
lean_dec(v_entry_1409_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1431_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v_dir_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1430_; 
v_dir_1419_ = lean_ctor_get(v_src_1410_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_src_1410_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1421_ = v_src_1410_;
v_isShared_1422_ = v_isSharedCheck_1430_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_dir_1419_);
lean_dec(v_src_1410_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1430_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1423_ = l_Lake_joinRelative(v_pkgDir_1408_, v_dir_1419_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1423_);
v___x_1425_ = v___x_1421_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
lean_object* v___x_1427_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 4, v___x_1425_);
v___x_1427_ = v___x_1417_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_name_1411_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_scope_1412_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v_configFile_1414_);
lean_ctor_set(v_reuseFailAlloc_1428_, 3, v_manifestFile_x3f_1415_);
lean_ctor_set(v_reuseFailAlloc_1428_, 4, v___x_1425_);
lean_ctor_set_uint8(v_reuseFailAlloc_1428_, sizeof(void*)*5, v_inherited_1413_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
}
else
{
lean_dec_ref(v_src_1410_);
lean_dec_ref(v_pkgDir_1408_);
return v_entry_1409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(lean_object* v_x_1433_){
_start:
{
if (lean_obj_tag(v_x_1433_) == 0)
{
lean_object* v_name_1434_; uint8_t v_inherited_1435_; lean_object* v_dir_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v_name_1434_ = lean_ctor_get(v_x_1433_, 0);
v_inherited_1435_ = lean_ctor_get_uint8(v_x_1433_, sizeof(void*)*3);
v_dir_1436_ = lean_ctor_get(v_x_1433_, 2);
v___x_1437_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_1438_ = l_Lake_defaultConfigFile;
v___x_1439_ = lean_box(0);
lean_inc_ref(v_dir_1436_);
v___x_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1440_, 0, v_dir_1436_);
lean_inc(v_name_1434_);
v___x_1441_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1441_, 0, v_name_1434_);
lean_ctor_set(v___x_1441_, 1, v___x_1437_);
lean_ctor_set(v___x_1441_, 2, v___x_1438_);
lean_ctor_set(v___x_1441_, 3, v___x_1439_);
lean_ctor_set(v___x_1441_, 4, v___x_1440_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*5, v_inherited_1435_);
return v___x_1441_;
}
else
{
lean_object* v_name_1442_; uint8_t v_inherited_1443_; lean_object* v_url_1444_; lean_object* v_rev_1445_; lean_object* v_inputRev_x3f_1446_; lean_object* v_subDir_x3f_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v_name_1442_ = lean_ctor_get(v_x_1433_, 0);
v_inherited_1443_ = lean_ctor_get_uint8(v_x_1433_, sizeof(void*)*6);
v_url_1444_ = lean_ctor_get(v_x_1433_, 2);
v_rev_1445_ = lean_ctor_get(v_x_1433_, 3);
v_inputRev_x3f_1446_ = lean_ctor_get(v_x_1433_, 4);
v_subDir_x3f_1447_ = lean_ctor_get(v_x_1433_, 5);
v___x_1448_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_1449_ = l_Lake_defaultConfigFile;
v___x_1450_ = lean_box(0);
lean_inc(v_subDir_x3f_1447_);
lean_inc(v_inputRev_x3f_1446_);
lean_inc_ref(v_rev_1445_);
lean_inc_ref(v_url_1444_);
v___x_1451_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1451_, 0, v_url_1444_);
lean_ctor_set(v___x_1451_, 1, v_rev_1445_);
lean_ctor_set(v___x_1451_, 2, v_inputRev_x3f_1446_);
lean_ctor_set(v___x_1451_, 3, v_subDir_x3f_1447_);
lean_inc(v_name_1442_);
v___x_1452_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1452_, 0, v_name_1442_);
lean_ctor_set(v___x_1452_, 1, v___x_1448_);
lean_ctor_set(v___x_1452_, 2, v___x_1449_);
lean_ctor_set(v___x_1452_, 3, v___x_1450_);
lean_ctor_set(v___x_1452_, 4, v___x_1451_);
lean_ctor_set_uint8(v___x_1452_, sizeof(void*)*5, v_inherited_1443_);
return v___x_1452_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6___boxed(lean_object* v_x_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(v_x_1453_);
lean_dec_ref(v_x_1453_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_addPackage(lean_object* v_entry_1455_, lean_object* v_self_1456_){
_start:
{
lean_object* v_name_1457_; lean_object* v_lakeDir_1458_; uint8_t v_fixedToolchain_1459_; lean_object* v_packagesDir_x3f_1460_; lean_object* v_packages_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1469_; 
v_name_1457_ = lean_ctor_get(v_self_1456_, 0);
v_lakeDir_1458_ = lean_ctor_get(v_self_1456_, 1);
v_fixedToolchain_1459_ = lean_ctor_get_uint8(v_self_1456_, sizeof(void*)*4);
v_packagesDir_x3f_1460_ = lean_ctor_get(v_self_1456_, 2);
v_packages_1461_ = lean_ctor_get(v_self_1456_, 3);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_self_1456_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1463_ = v_self_1456_;
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_packages_1461_);
lean_inc(v_packagesDir_x3f_1460_);
lean_inc(v_lakeDir_1458_);
lean_inc(v_name_1457_);
lean_dec(v_self_1456_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; lean_object* v___x_1467_; 
v___x_1465_ = lean_array_push(v_packages_1461_, v_entry_1455_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 3, v___x_1465_);
v___x_1467_ = v___x_1463_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_name_1457_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_lakeDir_1458_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_packagesDir_x3f_1460_);
lean_ctor_set(v_reuseFailAlloc_1468_, 3, v___x_1465_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*4, v_fixedToolchain_1459_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(size_t v_sz_1470_, size_t v_i_1471_, lean_object* v_bs_1472_){
_start:
{
uint8_t v___x_1473_; 
v___x_1473_ = lean_usize_dec_lt(v_i_1471_, v_sz_1470_);
if (v___x_1473_ == 0)
{
return v_bs_1472_;
}
else
{
lean_object* v_v_1474_; lean_object* v___x_1475_; lean_object* v_bs_x27_1476_; lean_object* v___x_1477_; size_t v___x_1478_; size_t v___x_1479_; lean_object* v___x_1480_; 
v_v_1474_ = lean_array_uget(v_bs_1472_, v_i_1471_);
v___x_1475_ = lean_unsigned_to_nat(0u);
v_bs_x27_1476_ = lean_array_uset(v_bs_1472_, v_i_1471_, v___x_1475_);
v___x_1477_ = l_Lake_PackageEntry_toJson(v_v_1474_);
v___x_1478_ = ((size_t)1ULL);
v___x_1479_ = lean_usize_add(v_i_1471_, v___x_1478_);
v___x_1480_ = lean_array_uset(v_bs_x27_1476_, v_i_1471_, v___x_1477_);
v_i_1471_ = v___x_1479_;
v_bs_1472_ = v___x_1480_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1482_, lean_object* v_i_1483_, lean_object* v_bs_1484_){
_start:
{
size_t v_sz_boxed_1485_; size_t v_i_boxed_1486_; lean_object* v_res_1487_; 
v_sz_boxed_1485_ = lean_unbox_usize(v_sz_1482_);
lean_dec(v_sz_1482_);
v_i_boxed_1486_ = lean_unbox_usize(v_i_1483_);
lean_dec(v_i_1483_);
v_res_1487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(v_sz_boxed_1485_, v_i_boxed_1486_, v_bs_1484_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lake_Manifest_toJson_spec__0(lean_object* v_a_1488_){
_start:
{
size_t v_sz_1489_; size_t v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v_sz_1489_ = lean_array_size(v_a_1488_);
v___x_1490_ = ((size_t)0ULL);
v___x_1491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(v_sz_1489_, v___x_1490_, v_a_1488_);
v___x_1492_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
return v___x_1492_;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__1(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = ((lean_object*)(l_Lake_Manifest_version___closed__2));
v___x_1495_ = l_Lake_StdVer_toString(v___x_1494_);
return v___x_1495_;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__2(void){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__1, &l_Lake_Manifest_toJson___closed__1_once, _init_l_Lake_Manifest_toJson___closed__1);
v___x_1497_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
return v___x_1497_;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__3(void){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1498_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__2, &l_Lake_Manifest_toJson___closed__2_once, _init_l_Lake_Manifest_toJson___closed__2);
v___x_1499_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__0));
v___x_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
lean_ctor_set(v___x_1500_, 1, v___x_1498_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_toJson(lean_object* v_self_1505_){
_start:
{
lean_object* v_name_1506_; lean_object* v_lakeDir_1507_; uint8_t v_fixedToolchain_1508_; lean_object* v_packagesDir_x3f_1509_; lean_object* v_packages_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; uint8_t v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v_name_1506_ = lean_ctor_get(v_self_1505_, 0);
lean_inc(v_name_1506_);
v_lakeDir_1507_ = lean_ctor_get(v_self_1505_, 1);
lean_inc_ref(v_lakeDir_1507_);
v_fixedToolchain_1508_ = lean_ctor_get_uint8(v_self_1505_, sizeof(void*)*4);
v_packagesDir_x3f_1509_ = lean_ctor_get(v_self_1505_, 2);
lean_inc(v_packagesDir_x3f_1509_);
v_packages_1510_ = lean_ctor_get(v_self_1505_, 3);
lean_inc_ref(v_packages_1510_);
lean_dec_ref(v_self_1505_);
v___x_1511_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__3, &l_Lake_Manifest_toJson___closed__3_once, _init_l_Lake_Manifest_toJson___closed__3);
v___x_1512_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__4));
v___x_1513_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1513_, 0, v_fixedToolchain_1508_);
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1512_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_1516_ = 1;
v___x_1517_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1506_, v___x_1516_);
v___x_1518_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
v___x_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1515_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__5));
v___x_1521_ = l_Lake_mkRelPathString(v_lakeDir_1507_);
v___x_1522_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
v___x_1523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1520_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___x_1524_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__6));
v___x_1525_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_packagesDir_x3f_1509_);
v___x_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__7));
v___x_1528_ = l_Array_toJson___at___00Lake_Manifest_toJson_spec__0(v_packages_1510_);
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = lean_box(0);
v___x_1531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1529_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1526_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1523_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1519_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v___x_1535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1514_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
v___x_1536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1511_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = l_Lean_Json_mkObj(v___x_1536_);
lean_dec_ref_known(v___x_1536_, 2);
return v___x_1537_;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6(void){
_start:
{
lean_object* v_natZero_1548_; lean_object* v_intZero_1549_; 
v_natZero_1548_ = lean_unsigned_to_nat(0u);
v_intZero_1549_ = lean_nat_to_int(v_natZero_1548_);
return v_intZero_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(lean_object* v_obj_1555_){
_start:
{
lean_object* v___y_1557_; lean_object* v_ver_1565_; lean_object* v_major_1566_; lean_object* v_ver_1583_; lean_object* v_a_1592_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__0));
v___x_1619_ = l_Lake_JsonObject_getJson_x3f(v_obj_1555_, v___x_1618_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8));
v___x_1621_ = l_Lake_JsonObject_getJson_x3f(v_obj_1555_, v___x_1620_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v___x_1622_; 
v___x_1622_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__10));
return v___x_1622_;
}
else
{
lean_object* v_val_1623_; 
v_val_1623_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_val_1623_);
lean_dec_ref_known(v___x_1621_, 1);
v_a_1592_ = v_val_1623_;
goto v___jp_1591_;
}
}
else
{
lean_object* v_val_1624_; 
v_val_1624_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_val_1624_);
lean_dec_ref_known(v___x_1619_, 1);
v_a_1592_ = v_val_1624_;
goto v___jp_1591_;
}
v___jp_1556_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1558_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__0));
v___x_1559_ = l_Lake_SemVerCore_toString(v___y_1557_);
v___x_1560_ = lean_string_append(v___x_1558_, v___x_1559_);
lean_dec_ref(v___x_1559_);
v___x_1561_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1562_ = lean_string_append(v___x_1560_, v___x_1561_);
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
return v___x_1563_;
}
v___jp_1564_:
{
lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1567_ = lean_unsigned_to_nat(1u);
v___x_1568_ = lean_nat_dec_lt(v___x_1567_, v_major_1566_);
lean_dec(v_major_1566_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1569_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__1));
v___x_1570_ = l_Lake_instOrdSemVerCore_ord(v_ver_1565_, v___x_1569_);
if (v___x_1570_ == 0)
{
v___y_1557_ = v_ver_1565_;
goto v___jp_1556_;
}
else
{
if (v___x_1568_ == 0)
{
lean_object* v___x_1571_; 
v___x_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1571_, 0, v_ver_1565_);
return v___x_1571_;
}
else
{
v___y_1557_ = v_ver_1565_;
goto v___jp_1556_;
}
}
}
else
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1572_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__2));
v___x_1573_ = l_Lake_SemVerCore_toString(v_ver_1565_);
v___x_1574_ = lean_string_append(v___x_1572_, v___x_1573_);
lean_dec_ref(v___x_1573_);
v___x_1575_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__3));
v___x_1576_ = lean_string_append(v___x_1574_, v___x_1575_);
v___x_1577_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__1, &l_Lake_Manifest_toJson___closed__1_once, _init_l_Lake_Manifest_toJson___closed__1);
v___x_1578_ = lean_string_append(v___x_1576_, v___x_1577_);
v___x_1579_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4));
v___x_1580_ = lean_string_append(v___x_1578_, v___x_1579_);
v___x_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
return v___x_1581_;
}
}
v___jp_1582_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1584_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__5));
v___x_1585_ = lean_unsigned_to_nat(80u);
v___x_1586_ = l_Lean_Json_pretty(v_ver_1583_, v___x_1585_);
v___x_1587_ = lean_string_append(v___x_1584_, v___x_1586_);
lean_dec_ref(v___x_1586_);
v___x_1588_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4));
v___x_1589_ = lean_string_append(v___x_1587_, v___x_1588_);
v___x_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
return v___x_1590_;
}
v___jp_1591_:
{
switch(lean_obj_tag(v_a_1592_))
{
case 2:
{
lean_object* v_n_1593_; lean_object* v_mantissa_1594_; lean_object* v_exponent_1595_; lean_object* v_natZero_1596_; lean_object* v_intZero_1597_; uint8_t v_isNeg_1598_; 
v_n_1593_ = lean_ctor_get(v_a_1592_, 0);
v_mantissa_1594_ = lean_ctor_get(v_n_1593_, 0);
v_exponent_1595_ = lean_ctor_get(v_n_1593_, 1);
v_natZero_1596_ = lean_unsigned_to_nat(0u);
v_intZero_1597_ = lean_obj_once(&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6, &l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6_once, _init_l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6);
v_isNeg_1598_ = lean_int_dec_lt(v_mantissa_1594_, v_intZero_1597_);
if (v_isNeg_1598_ == 0)
{
uint8_t v___x_1599_; 
v___x_1599_ = lean_nat_dec_eq(v_exponent_1595_, v_natZero_1596_);
if (v___x_1599_ == 0)
{
v_ver_1583_ = v_a_1592_;
goto v___jp_1582_;
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1601_; 
lean_inc(v_mantissa_1594_);
lean_dec_ref_known(v_a_1592_, 1);
v_a_1600_ = lean_nat_abs(v_mantissa_1594_);
lean_dec(v_mantissa_1594_);
v___x_1601_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1601_, 0, v_natZero_1596_);
lean_ctor_set(v___x_1601_, 1, v_a_1600_);
lean_ctor_set(v___x_1601_, 2, v_natZero_1596_);
v_ver_1565_ = v___x_1601_;
v_major_1566_ = v_natZero_1596_;
goto v___jp_1564_;
}
}
else
{
v_ver_1583_ = v_a_1592_;
goto v___jp_1582_;
}
}
case 3:
{
lean_object* v_s_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v_s_1602_ = lean_ctor_get(v_a_1592_, 0);
lean_inc_ref(v_s_1602_);
lean_dec_ref_known(v_a_1592_, 1);
v___x_1603_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7));
v___x_1604_ = lean_unsigned_to_nat(0u);
v___x_1605_ = lean_string_utf8_byte_size(v_s_1602_);
v___x_1606_ = l___private_Lake_Util_Version_0__Lake_runVerParse(lean_box(0), v_s_1602_, v___x_1603_, v___x_1604_, v___x_1605_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1606_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1606_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v_toSemVerCore_1616_; lean_object* v_major_1617_; 
v_a_1615_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1615_);
lean_dec_ref_known(v___x_1606_, 1);
v_toSemVerCore_1616_ = lean_ctor_get(v_a_1615_, 0);
lean_inc_ref(v_toSemVerCore_1616_);
lean_dec(v_a_1615_);
v_major_1617_ = lean_ctor_get(v_toSemVerCore_1616_, 0);
lean_inc(v_major_1617_);
v_ver_1565_ = v_toSemVerCore_1616_;
v_major_1566_ = v_major_1617_;
goto v___jp_1564_;
}
}
default: 
{
v_ver_1583_ = v_a_1592_;
goto v___jp_1582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___boxed(lean_object* v_obj_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_obj_1625_);
lean_dec(v_obj_1625_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(size_t v_sz_1627_, size_t v_i_1628_, lean_object* v_bs_1629_){
_start:
{
uint8_t v___x_1630_; 
v___x_1630_ = lean_usize_dec_lt(v_i_1628_, v_sz_1627_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; 
v___x_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1631_, 0, v_bs_1629_);
return v___x_1631_;
}
else
{
lean_object* v_v_1632_; lean_object* v___x_1633_; 
v_v_1632_ = lean_array_uget_borrowed(v_bs_1629_, v_i_1628_);
lean_inc(v_v_1632_);
v___x_1633_ = l_Lake_PackageEntry_fromJson_x3f(v_v_1632_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
lean_dec_ref(v_bs_1629_);
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1633_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1643_; lean_object* v_bs_x27_1644_; size_t v___x_1645_; size_t v___x_1646_; lean_object* v___x_1647_; 
v_a_1642_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1633_, 1);
v___x_1643_ = lean_unsigned_to_nat(0u);
v_bs_x27_1644_ = lean_array_uset(v_bs_1629_, v_i_1628_, v___x_1643_);
v___x_1645_ = ((size_t)1ULL);
v___x_1646_ = lean_usize_add(v_i_1628_, v___x_1645_);
v___x_1647_ = lean_array_uset(v_bs_x27_1644_, v_i_1628_, v_a_1642_);
v_i_1628_ = v___x_1646_;
v_bs_1629_ = v___x_1647_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_1649_, lean_object* v_i_1650_, lean_object* v_bs_1651_){
_start:
{
size_t v_sz_boxed_1652_; size_t v_i_boxed_1653_; lean_object* v_res_1654_; 
v_sz_boxed_1652_ = lean_unbox_usize(v_sz_1649_);
lean_dec(v_sz_1649_);
v_i_boxed_1653_ = lean_unbox_usize(v_i_1650_);
lean_dec(v_i_1650_);
v_res_1654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(v_sz_boxed_1652_, v_i_boxed_1653_, v_bs_1651_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1(lean_object* v_x_1656_){
_start:
{
if (lean_obj_tag(v_x_1656_) == 4)
{
lean_object* v_elems_1657_; size_t v_sz_1658_; size_t v___x_1659_; lean_object* v___x_1660_; 
v_elems_1657_ = lean_ctor_get(v_x_1656_, 0);
lean_inc_ref(v_elems_1657_);
lean_dec_ref_known(v_x_1656_, 1);
v_sz_1658_ = lean_array_size(v_elems_1657_);
v___x_1659_ = ((size_t)0ULL);
v___x_1660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(v_sz_1658_, v___x_1659_, v_elems_1657_);
return v___x_1660_;
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1661_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1___closed__0));
v___x_1662_ = lean_unsigned_to_nat(80u);
v___x_1663_ = l_Lean_Json_pretty(v_x_1656_, v___x_1662_);
v___x_1664_ = lean_string_append(v___x_1661_, v___x_1663_);
lean_dec_ref(v___x_1663_);
v___x_1665_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1666_ = lean_string_append(v___x_1664_, v___x_1665_);
v___x_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
return v___x_1667_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1(lean_object* v_x_1670_){
_start:
{
if (lean_obj_tag(v_x_1670_) == 0)
{
lean_object* v___x_1671_; 
v___x_1671_ = ((lean_object*)(l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1___closed__0));
return v___x_1671_;
}
else
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1(v_x_1670_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1689_; 
v_a_1681_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1683_ = v___x_1672_;
v_isShared_1684_ = v_isSharedCheck_1689_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1672_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1689_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1685_, 0, v_a_1681_);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v___x_1685_);
v___x_1687_ = v___x_1683_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(size_t v_sz_1690_, size_t v_i_1691_, lean_object* v_bs_1692_){
_start:
{
uint8_t v___x_1693_; 
v___x_1693_ = lean_usize_dec_lt(v_i_1691_, v_sz_1690_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; 
v___x_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1694_, 0, v_bs_1692_);
return v___x_1694_;
}
else
{
lean_object* v_v_1695_; lean_object* v___x_1696_; 
v_v_1695_ = lean_array_uget_borrowed(v_bs_1692_, v_i_1691_);
lean_inc(v_v_1695_);
v___x_1696_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson(v_v_1695_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec_ref(v_bs_1692_);
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1696_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1696_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1706_; lean_object* v_bs_x27_1707_; size_t v___x_1708_; size_t v___x_1709_; lean_object* v___x_1710_; 
v_a_1705_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1705_);
lean_dec_ref_known(v___x_1696_, 1);
v___x_1706_ = lean_unsigned_to_nat(0u);
v_bs_x27_1707_ = lean_array_uset(v_bs_1692_, v_i_1691_, v___x_1706_);
v___x_1708_ = ((size_t)1ULL);
v___x_1709_ = lean_usize_add(v_i_1691_, v___x_1708_);
v___x_1710_ = lean_array_uset(v_bs_x27_1707_, v_i_1691_, v_a_1705_);
v_i_1691_ = v___x_1709_;
v_bs_1692_ = v___x_1710_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_1712_, lean_object* v_i_1713_, lean_object* v_bs_1714_){
_start:
{
size_t v_sz_boxed_1715_; size_t v_i_boxed_1716_; lean_object* v_res_1717_; 
v_sz_boxed_1715_ = lean_unbox_usize(v_sz_1712_);
lean_dec(v_sz_1712_);
v_i_boxed_1716_ = lean_unbox_usize(v_i_1713_);
lean_dec(v_i_1713_);
v_res_1717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(v_sz_boxed_1715_, v_i_boxed_1716_, v_bs_1714_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3(lean_object* v_x_1718_){
_start:
{
if (lean_obj_tag(v_x_1718_) == 4)
{
lean_object* v_elems_1719_; size_t v_sz_1720_; size_t v___x_1721_; lean_object* v___x_1722_; 
v_elems_1719_ = lean_ctor_get(v_x_1718_, 0);
lean_inc_ref(v_elems_1719_);
lean_dec_ref_known(v_x_1718_, 1);
v_sz_1720_ = lean_array_size(v_elems_1719_);
v___x_1721_ = ((size_t)0ULL);
v___x_1722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(v_sz_1720_, v___x_1721_, v_elems_1719_);
return v___x_1722_;
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1723_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1___closed__0));
v___x_1724_ = lean_unsigned_to_nat(80u);
v___x_1725_ = l_Lean_Json_pretty(v_x_1718_, v___x_1724_);
v___x_1726_ = lean_string_append(v___x_1723_, v___x_1725_);
lean_dec_ref(v___x_1725_);
v___x_1727_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1728_ = lean_string_append(v___x_1726_, v___x_1727_);
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
return v___x_1729_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2(lean_object* v_x_1732_){
_start:
{
if (lean_obj_tag(v_x_1732_) == 0)
{
lean_object* v___x_1733_; 
v___x_1733_ = ((lean_object*)(l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2___closed__0));
return v___x_1733_;
}
else
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3(v_x_1732_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1734_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1734_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1751_; 
v_a_1743_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1745_ = v___x_1734_;
v_isShared_1746_ = v_isSharedCheck_1751_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1734_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1751_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1747_, 0, v_a_1743_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1747_);
v___x_1749_ = v___x_1745_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(size_t v_sz_1752_, size_t v_i_1753_, lean_object* v_bs_1754_){
_start:
{
uint8_t v___x_1755_; 
v___x_1755_ = lean_usize_dec_lt(v_i_1753_, v_sz_1752_);
if (v___x_1755_ == 0)
{
return v_bs_1754_;
}
else
{
lean_object* v_v_1756_; lean_object* v___x_1757_; lean_object* v_bs_x27_1758_; lean_object* v___x_1759_; size_t v___x_1760_; size_t v___x_1761_; lean_object* v___x_1762_; 
v_v_1756_ = lean_array_uget(v_bs_1754_, v_i_1753_);
v___x_1757_ = lean_unsigned_to_nat(0u);
v_bs_x27_1758_ = lean_array_uset(v_bs_1754_, v_i_1753_, v___x_1757_);
v___x_1759_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(v_v_1756_);
lean_dec(v_v_1756_);
v___x_1760_ = ((size_t)1ULL);
v___x_1761_ = lean_usize_add(v_i_1753_, v___x_1760_);
v___x_1762_ = lean_array_uset(v_bs_x27_1758_, v_i_1753_, v___x_1759_);
v_i_1753_ = v___x_1761_;
v_bs_1754_ = v___x_1762_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0___boxed(lean_object* v_sz_1764_, lean_object* v_i_1765_, lean_object* v_bs_1766_){
_start:
{
size_t v_sz_boxed_1767_; size_t v_i_boxed_1768_; lean_object* v_res_1769_; 
v_sz_boxed_1767_ = lean_unbox_usize(v_sz_1764_);
lean_dec(v_sz_1764_);
v_i_boxed_1768_ = lean_unbox_usize(v_i_1765_);
lean_dec(v_i_1765_);
v_res_1769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(v_sz_boxed_1767_, v_i_boxed_1768_, v_bs_1766_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(lean_object* v_ver_1783_, lean_object* v_obj_1784_){
_start:
{
lean_object* v_a_1786_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1795_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__4));
v___x_1796_ = l_Lake_StdVer_compare(v_ver_1783_, v___x_1795_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__7));
v___x_1798_ = l_Lake_JsonObject_getJson_x3f(v_obj_1784_, v___x_1797_);
if (lean_obj_tag(v___x_1798_) == 0)
{
goto v___jp_1791_;
}
else
{
lean_object* v_val_1799_; lean_object* v___x_1800_; 
v_val_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_val_1799_);
lean_dec_ref_known(v___x_1798_, 1);
v___x_1800_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2(v_val_1799_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1810_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1810_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1810_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1805_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5));
v___x_1806_ = lean_string_append(v___x_1805_, v_a_1801_);
lean_dec(v_a_1801_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v___x_1806_);
v___x_1808_ = v___x_1803_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
else
{
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
v_a_1811_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1800_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1800_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
lean_ctor_set_tag(v___x_1813_, 0);
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
else
{
lean_object* v_a_1819_; 
v_a_1819_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_a_1819_);
lean_dec_ref_known(v___x_1800_, 1);
if (lean_obj_tag(v_a_1819_) == 0)
{
goto v___jp_1791_;
}
else
{
lean_object* v_val_1820_; 
v_val_1820_ = lean_ctor_get(v_a_1819_, 0);
lean_inc(v_val_1820_);
lean_dec_ref_known(v_a_1819_, 1);
v_a_1786_ = v_val_1820_;
goto v___jp_1785_;
}
}
}
}
}
else
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__7));
v___x_1822_ = l_Lake_JsonObject_getJson_x3f(v_obj_1784_, v___x_1821_);
if (lean_obj_tag(v___x_1822_) == 0)
{
goto v___jp_1793_;
}
else
{
lean_object* v_val_1823_; lean_object* v___x_1824_; 
v_val_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_val_1823_);
lean_dec_ref_known(v___x_1822_, 1);
v___x_1824_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1(v_val_1823_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1834_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1827_ = v___x_1824_;
v_isShared_1828_ = v_isSharedCheck_1834_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1834_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1832_; 
v___x_1829_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5));
v___x_1830_ = lean_string_append(v___x_1829_, v_a_1825_);
lean_dec(v_a_1825_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1830_);
v___x_1832_ = v___x_1827_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1830_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
else
{
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
v_a_1835_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1824_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1824_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
lean_ctor_set_tag(v___x_1837_, 0);
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1851_; 
v_a_1843_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1845_ = v___x_1824_;
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1824_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
if (lean_obj_tag(v_a_1843_) == 0)
{
lean_del_object(v___x_1845_);
goto v___jp_1793_;
}
else
{
lean_object* v_val_1847_; lean_object* v___x_1849_; 
v_val_1847_ = lean_ctor_get(v_a_1843_, 0);
lean_inc(v_val_1847_);
lean_dec_ref_known(v_a_1843_, 1);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v_val_1847_);
v___x_1849_ = v___x_1845_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_val_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
}
}
}
v___jp_1785_:
{
size_t v_sz_1787_; size_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v_sz_1787_ = lean_array_size(v_a_1786_);
v___x_1788_ = ((size_t)0ULL);
v___x_1789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(v_sz_1787_, v___x_1788_, v_a_1786_);
v___x_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
return v___x_1790_;
}
v___jp_1791_:
{
lean_object* v___x_1792_; 
v___x_1792_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__0));
v_a_1786_ = v___x_1792_;
goto v___jp_1785_;
}
v___jp_1793_:
{
lean_object* v___x_1794_; 
v___x_1794_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__2));
return v___x_1794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___boxed(lean_object* v_ver_1852_, lean_object* v_obj_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(v_ver_1852_, v_obj_1853_);
lean_dec(v_obj_1853_);
lean_dec_ref(v_ver_1852_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0(lean_object* v_x_1857_){
_start:
{
if (lean_obj_tag(v_x_1857_) == 0)
{
lean_object* v___x_1858_; 
v___x_1858_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0___closed__0));
return v___x_1858_;
}
else
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Lean_Name_fromJson_x3f(v_x_1857_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1876_; 
v_a_1868_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1870_ = v___x_1859_;
v_isShared_1871_ = v_isSharedCheck_1876_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1859_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1876_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1872_, 0, v_a_1868_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v___x_1872_);
v___x_1874_ = v___x_1870_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1(lean_object* v_x_1879_){
_start:
{
if (lean_obj_tag(v_x_1879_) == 0)
{
lean_object* v___x_1880_; 
v___x_1880_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1___closed__0));
return v___x_1880_;
}
else
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_Json_getBool_x3f(v_x_1879_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1881_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1881_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1898_; 
v_a_1890_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1892_ = v___x_1881_;
v_isShared_1893_ = v_isSharedCheck_1898_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1881_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1898_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1894_, 0, v_a_1890_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v___x_1894_);
v___x_1896_ = v___x_1892_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1___boxed(lean_object* v_x_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1(v_x_1899_);
lean_dec(v_x_1899_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_fromJson_x3f(lean_object* v_json_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Lean_Json_getObj_x3f(v_json_1904_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1905_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1905_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1915_; 
v_a_1914_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___x_1905_, 1);
v___x_1915_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_a_1914_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec(v_a_1914_);
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1915_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1915_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
else
{
lean_object* v_a_1924_; uint8_t v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v_a_1929_; uint8_t v___y_1951_; lean_object* v___y_1952_; lean_object* v_a_1953_; uint8_t v___y_1979_; lean_object* v___y_1980_; uint8_t v___y_1983_; lean_object* v_a_1984_; uint8_t v___y_2010_; uint8_t v_a_2013_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v_a_1924_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1915_, 1);
v___x_2040_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__4));
v___x_2041_ = l_Lake_JsonObject_getJson_x3f(v_a_1914_, v___x_2040_);
if (lean_obj_tag(v___x_2041_) == 0)
{
goto v___jp_2038_;
}
else
{
lean_object* v_val_2042_; lean_object* v___x_2043_; 
v_val_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_val_2042_);
lean_dec_ref_known(v___x_2041_, 1);
v___x_2043_ = l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1(v_val_2042_);
lean_dec(v_val_2042_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2053_; 
lean_dec(v_a_1924_);
lean_dec(v_a_1914_);
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2046_ = v___x_2043_;
v_isShared_2047_ = v_isSharedCheck_2053_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2043_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2053_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2051_; 
v___x_2048_ = ((lean_object*)(l_Lake_Manifest_fromJson_x3f___closed__2));
v___x_2049_ = lean_string_append(v___x_2048_, v_a_2044_);
lean_dec(v_a_2044_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v___x_2049_);
v___x_2051_ = v___x_2046_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
else
{
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_dec(v_a_1924_);
lean_dec(v_a_1914_);
v_a_2054_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2043_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2043_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
lean_ctor_set_tag(v___x_2056_, 0);
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
else
{
lean_object* v_a_2062_; 
v_a_2062_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2043_, 1);
if (lean_obj_tag(v_a_2062_) == 0)
{
goto v___jp_2038_;
}
else
{
lean_object* v_val_2063_; uint8_t v___x_2064_; 
v_val_2063_ = lean_ctor_get(v_a_2062_, 0);
lean_inc(v_val_2063_);
lean_dec_ref_known(v_a_2062_, 1);
v___x_2064_ = lean_unbox(v_val_2063_);
lean_dec(v_val_2063_);
v_a_2013_ = v___x_2064_;
goto v___jp_2012_;
}
}
}
}
v___jp_1925_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1931_, 0, v_a_1924_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(v___x_1931_, v_a_1914_);
lean_dec(v_a_1914_);
lean_dec_ref_known(v___x_1931_, 2);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec(v_a_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1932_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1932_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1949_; 
v_a_1941_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1943_ = v___x_1932_;
v_isShared_1944_ = v_isSharedCheck_1949_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1932_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1949_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1945_; lean_object* v___x_1947_; 
v___x_1945_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1945_, 0, v___y_1928_);
lean_ctor_set(v___x_1945_, 1, v___y_1927_);
lean_ctor_set(v___x_1945_, 2, v_a_1929_);
lean_ctor_set(v___x_1945_, 3, v_a_1941_);
lean_ctor_set_uint8(v___x_1945_, sizeof(void*)*4, v___y_1926_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v___x_1945_);
v___x_1947_ = v___x_1943_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
v___jp_1950_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__6));
v___x_1955_ = l_Lake_JsonObject_getJson_x3f(v_a_1914_, v___x_1954_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v___x_1956_; 
v___x_1956_ = lean_box(0);
v___y_1926_ = v___y_1951_;
v___y_1927_ = v_a_1953_;
v___y_1928_ = v___y_1952_;
v_a_1929_ = v___x_1956_;
goto v___jp_1925_;
}
else
{
lean_object* v_val_1957_; lean_object* v___x_1958_; 
v_val_1957_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_val_1957_);
lean_dec_ref_known(v___x_1955_, 1);
v___x_1958_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1957_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1968_; 
lean_dec_ref(v_a_1953_);
lean_dec(v___y_1952_);
lean_dec(v_a_1924_);
lean_dec(v_a_1914_);
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_1968_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1968_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1966_; 
v___x_1963_ = ((lean_object*)(l_Lake_Manifest_fromJson_x3f___closed__0));
v___x_1964_ = lean_string_append(v___x_1963_, v_a_1959_);
lean_dec(v_a_1959_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v___x_1964_);
v___x_1966_ = v___x_1961_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1964_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
else
{
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_dec_ref(v_a_1953_);
lean_dec(v___y_1952_);
lean_dec(v_a_1924_);
lean_dec(v_a_1914_);
v_a_1969_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1958_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1958_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set_tag(v___x_1971_, 0);
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
else
{
lean_object* v_a_1977_; 
v_a_1977_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1977_);
lean_dec_ref_known(v___x_1958_, 1);
v___y_1926_ = v___y_1951_;
v___y_1927_ = v_a_1953_;
v___y_1928_ = v___y_1952_;
v_a_1929_ = v_a_1977_;
goto v___jp_1925_;
}
}
}
}
v___jp_1978_:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lake_defaultLakeDir;
v___y_1951_ = v___y_1979_;
v___y_1952_ = v___y_1980_;
v_a_1953_ = v___x_1981_;
goto v___jp_1950_;
}
v___jp_1982_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__5));
v___x_1986_ = l_Lake_JsonObject_getJson_x3f(v_a_1914_, v___x_1985_);
if (lean_obj_tag(v___x_1986_) == 0)
{
v___y_1979_ = v___y_1983_;
v___y_1980_ = v_a_1984_;
goto v___jp_1978_;
}
else
{
lean_object* v_val_1987_; lean_object* v___x_1988_; 
v_val_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_val_1987_);
lean_dec_ref_known(v___x_1986_, 1);
v___x_1988_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1987_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1998_; 
lean_dec(v_a_1984_);
lean_dec(v_a_1924_);
lean_dec(v_a_1914_);
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1991_ = v___x_1988_;
v_isShared_1992_ = v_isSharedCheck_1998_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1988_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1998_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1993_ = ((lean_object*)(l_Lake_Manifest_fromJson_x3f___closed__1));
v___x_1994_ = lean_string_append(v___x_1993_, v_a_1989_);
lean_dec(v_a_1989_);
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v___x_1994_);
v___x_1996_ = v___x_1991_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
else
{
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec(v_a_1984_);
lean_dec(v_a_1924_);
lean_dec(v_a_1914_);
v_a_1999_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1988_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1988_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set_tag(v___x_2001_, 0);
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
else
{
lean_object* v_a_2007_; 
v_a_2007_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_1988_, 1);
if (lean_obj_tag(v_a_2007_) == 0)
{
v___y_1979_ = v___y_1983_;
v___y_1980_ = v_a_1984_;
goto v___jp_1978_;
}
else
{
lean_object* v_val_2008_; 
v_val_2008_ = lean_ctor_get(v_a_2007_, 0);
lean_inc(v_val_2008_);
lean_dec_ref_known(v_a_2007_, 1);
v___y_1951_ = v___y_1983_;
v___y_1952_ = v_a_1984_;
v_a_1953_ = v_val_2008_;
goto v___jp_1950_;
}
}
}
}
}
v___jp_2009_:
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_box(0);
v___y_1983_ = v___y_2010_;
v_a_1984_ = v___x_2011_;
goto v___jp_1982_;
}
v___jp_2012_:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_2015_ = l_Lake_JsonObject_getJson_x3f(v_a_1914_, v___x_2014_);
if (lean_obj_tag(v___x_2015_) == 0)
{
v___y_2010_ = v_a_2013_;
goto v___jp_2009_;
}
else
{
lean_object* v_val_2016_; lean_object* v___x_2017_; 
v_val_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_val_2016_);
lean_dec_ref_known(v___x_2015_, 1);
v___x_2017_ = l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0(v_val_2016_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v_a_1924_);
lean_dec(v_a_1914_);
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2020_ = v___x_2017_;
v_isShared_2021_ = v_isSharedCheck_2027_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2017_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2027_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2025_; 
v___x_2022_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__1));
v___x_2023_ = lean_string_append(v___x_2022_, v_a_2018_);
lean_dec(v_a_2018_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 0, v___x_2023_);
v___x_2025_ = v___x_2020_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
else
{
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_dec(v_a_1924_);
lean_dec(v_a_1914_);
v_a_2028_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2017_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2017_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set_tag(v___x_2030_, 0);
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
else
{
lean_object* v_a_2036_; 
v_a_2036_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2036_);
lean_dec_ref_known(v___x_2017_, 1);
if (lean_obj_tag(v_a_2036_) == 0)
{
v___y_2010_ = v_a_2013_;
goto v___jp_2009_;
}
else
{
lean_object* v_val_2037_; 
v_val_2037_ = lean_ctor_get(v_a_2036_, 0);
lean_inc(v_val_2037_);
lean_dec_ref_known(v_a_2036_, 1);
v___y_1983_ = v_a_2013_;
v_a_1984_ = v_val_2037_;
goto v___jp_1982_;
}
}
}
}
}
v___jp_2038_:
{
uint8_t v___x_2039_; 
v___x_2039_ = 0;
v_a_2013_ = v___x_2039_;
goto v___jp_2012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_parse(lean_object* v_data_2068_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Lean_Json_parse(v_data_2068_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2079_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2072_ = v___x_2069_;
v_isShared_2073_ = v_isSharedCheck_2079_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2069_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2079_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2074_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2075_ = lean_string_append(v___x_2074_, v_a_2070_);
lean_dec(v_a_2070_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 0, v___x_2075_);
v___x_2077_ = v___x_2072_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2081_; 
v_a_2080_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2080_);
lean_dec_ref_known(v___x_2069_, 1);
v___x_2081_ = l_Lake_Manifest_fromJson_x3f(v_a_2080_);
return v___x_2081_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load(lean_object* v_file_2083_){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_IO_FS_readFile(v_file_2083_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2114_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2088_ = v___x_2085_;
v_isShared_2089_ = v_isSharedCheck_2114_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2085_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2114_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v_a_2091_; lean_object* v___x_2099_; 
v___x_2099_ = l_Lean_Json_parse(v_a_2086_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2099_, 1);
v___x_2101_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2102_ = lean_string_append(v___x_2101_, v_a_2100_);
lean_dec(v_a_2100_);
v_a_2091_ = v___x_2102_;
goto v___jp_2090_;
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2104_; 
v_a_2103_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___x_2099_, 1);
v___x_2104_ = l_Lake_Manifest_fromJson_x3f(v_a_2103_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref_known(v___x_2104_, 1);
v_a_2091_ = v_a_2105_;
goto v___jp_2090_;
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_del_object(v___x_2088_);
lean_dec_ref(v_file_2083_);
v_a_2106_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2104_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2104_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
lean_ctor_set_tag(v___x_2108_, 0);
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
v___jp_2090_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2097_; 
v___x_2092_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2093_ = lean_string_append(v_file_2083_, v___x_2092_);
v___x_2094_ = lean_string_append(v___x_2093_, v_a_2091_);
lean_dec_ref(v_a_2091_);
v___x_2095_ = lean_mk_io_user_error(v___x_2094_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set_tag(v___x_2088_, 1);
lean_ctor_set(v___x_2088_, 0, v___x_2095_);
v___x_2097_ = v___x_2088_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
lean_dec_ref(v_file_2083_);
v_a_2115_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2085_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2085_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load___boxed(lean_object* v_file_2123_, lean_object* v_a_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Lake_Manifest_load(v_file_2123_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f(lean_object* v_file_2126_){
_start:
{
lean_object* v_a_2129_; lean_object* v___x_2133_; 
v___x_2133_ = l_IO_FS_readFile(v_file_2126_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2162_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2162_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2162_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v_a_2139_; lean_object* v___x_2144_; 
v___x_2144_ = l_Lean_Json_parse(v_a_2134_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
lean_del_object(v___x_2136_);
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2146_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2147_ = lean_string_append(v___x_2146_, v_a_2145_);
lean_dec(v_a_2145_);
v_a_2139_ = v___x_2147_;
goto v___jp_2138_;
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2149_; 
v_a_2148_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2148_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2149_ = l_Lake_Manifest_fromJson_x3f(v_a_2148_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; 
lean_del_object(v___x_2136_);
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2149_, 1);
v_a_2139_ = v_a_2150_;
goto v___jp_2138_;
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2161_; 
lean_dec_ref(v_file_2126_);
v_a_2151_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2153_ = v___x_2149_;
v_isShared_2154_ = v_isSharedCheck_2161_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2149_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2161_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2158_; 
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v___x_2156_);
v___x_2158_ = v___x_2136_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
}
v___jp_2138_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2140_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2141_ = lean_string_append(v_file_2126_, v___x_2140_);
v___x_2142_ = lean_string_append(v___x_2141_, v_a_2139_);
lean_dec_ref(v_a_2139_);
v___x_2143_ = lean_mk_io_user_error(v___x_2142_);
v_a_2129_ = v___x_2143_;
goto v___jp_2128_;
}
}
}
else
{
lean_object* v_a_2163_; 
lean_dec_ref(v_file_2126_);
v_a_2163_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2133_, 1);
v_a_2129_ = v_a_2163_;
goto v___jp_2128_;
}
v___jp_2128_:
{
if (lean_obj_tag(v_a_2129_) == 11)
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
lean_dec_ref_known(v_a_2129_, 2);
v___x_2130_ = lean_box(0);
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
return v___x_2131_;
}
else
{
lean_object* v___x_2132_; 
v___x_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2132_, 0, v_a_2129_);
return v___x_2132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f___boxed(lean_object* v_file_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Lake_Manifest_load_x3f(v_file_2164_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_save(lean_object* v_self_2167_, lean_object* v_manifestFile_2168_){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v_contents_2172_; uint32_t v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2170_ = l_Lake_Manifest_toJson(v_self_2167_);
v___x_2171_ = lean_unsigned_to_nat(80u);
v_contents_2172_ = l_Lean_Json_pretty(v___x_2170_, v___x_2171_);
v___x_2173_ = 10;
v___x_2174_ = lean_string_push(v_contents_2172_, v___x_2173_);
v___x_2175_ = l_IO_FS_writeFile(v_manifestFile_2168_, v___x_2174_);
lean_dec_ref(v___x_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_save___boxed(lean_object* v_self_2176_, lean_object* v_manifestFile_2177_, lean_object* v_a_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l_Lake_Manifest_save(v_self_2176_, v_manifestFile_2177_);
lean_dec_ref(v_manifestFile_2177_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_decodeEntries(lean_object* v_data_2180_){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = l_Lean_Json_getObj_x3f(v_data_2180_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2181_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2181_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2191_; 
v_a_2190_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2190_);
lean_dec_ref_known(v___x_2181_, 1);
v___x_2191_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_a_2190_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec(v_a_2190_);
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2191_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2191_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v_a_2200_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_a_2200_);
lean_dec_ref_known(v___x_2191_, 1);
v___x_2201_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2202_, 0, v_a_2200_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
v___x_2203_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(v___x_2202_, v_a_2190_);
lean_dec(v_a_2190_);
lean_dec_ref_known(v___x_2202_, 2);
return v___x_2203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_parseEntries(lean_object* v_data_2204_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Lean_Json_parse(v_data_2204_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2215_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2208_ = v___x_2205_;
v_isShared_2209_ = v_isSharedCheck_2215_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2205_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2215_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2210_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2211_ = lean_string_append(v___x_2210_, v_a_2206_);
lean_dec(v_a_2206_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2211_);
v___x_2213_ = v___x_2208_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2217_; 
v_a_2216_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2205_, 1);
v___x_2217_ = l_Lake_Manifest_decodeEntries(v_a_2216_);
return v___x_2217_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_loadEntries(lean_object* v_file_2218_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_IO_FS_readFile(v_file_2218_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2249_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2223_ = v___x_2220_;
v_isShared_2224_ = v_isSharedCheck_2249_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2220_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2249_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v_a_2226_; lean_object* v___x_2234_; 
v___x_2234_ = l_Lean_Json_parse(v_a_2221_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v___x_2234_, 1);
v___x_2236_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2237_ = lean_string_append(v___x_2236_, v_a_2235_);
lean_dec(v_a_2235_);
v_a_2226_ = v___x_2237_;
goto v___jp_2225_;
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2239_; 
v_a_2238_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2238_);
lean_dec_ref_known(v___x_2234_, 1);
v___x_2239_ = l_Lake_Manifest_decodeEntries(v_a_2238_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v___x_2239_, 1);
v_a_2226_ = v_a_2240_;
goto v___jp_2225_;
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_del_object(v___x_2223_);
lean_dec_ref(v_file_2218_);
v_a_2241_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2239_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2239_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
lean_ctor_set_tag(v___x_2243_, 0);
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
v___jp_2225_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2232_; 
v___x_2227_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2228_ = lean_string_append(v_file_2218_, v___x_2227_);
v___x_2229_ = lean_string_append(v___x_2228_, v_a_2226_);
lean_dec_ref(v_a_2226_);
v___x_2230_ = lean_mk_io_user_error(v___x_2229_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set_tag(v___x_2223_, 1);
lean_ctor_set(v___x_2223_, 0, v___x_2230_);
v___x_2232_ = v___x_2223_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2230_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec_ref(v_file_2218_);
v_a_2250_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2220_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2220_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_loadEntries___boxed(lean_object* v_file_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lake_Manifest_loadEntries(v_file_2258_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries(lean_object* v_file_2261_){
_start:
{
lean_object* v_a_2264_; lean_object* v___x_2273_; 
v___x_2273_ = l_IO_FS_readFile(v_file_2261_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2295_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2276_ = v___x_2273_;
v_isShared_2277_ = v_isSharedCheck_2295_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2273_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2295_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v_a_2279_; lean_object* v___x_2284_; 
v___x_2284_ = l_Lean_Json_parse(v_a_2274_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_del_object(v___x_2276_);
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref_known(v___x_2284_, 1);
v___x_2286_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2287_ = lean_string_append(v___x_2286_, v_a_2285_);
lean_dec(v_a_2285_);
v_a_2279_ = v___x_2287_;
goto v___jp_2278_;
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2289_; 
v_a_2288_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2284_, 1);
v___x_2289_ = l_Lake_Manifest_decodeEntries(v_a_2288_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; 
lean_del_object(v___x_2276_);
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2290_);
lean_dec_ref_known(v___x_2289_, 1);
v_a_2279_ = v_a_2290_;
goto v___jp_2278_;
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; 
lean_dec_ref(v_file_2261_);
v_a_2291_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2291_);
lean_dec_ref_known(v___x_2289_, 1);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 0, v_a_2291_);
v___x_2293_ = v___x_2276_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2291_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
v___jp_2278_:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2280_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
lean_inc_ref(v_file_2261_);
v___x_2281_ = lean_string_append(v_file_2261_, v___x_2280_);
v___x_2282_ = lean_string_append(v___x_2281_, v_a_2279_);
lean_dec_ref(v_a_2279_);
v___x_2283_ = lean_mk_io_user_error(v___x_2282_);
v_a_2264_ = v___x_2283_;
goto v___jp_2263_;
}
}
}
else
{
lean_object* v_a_2296_; 
v_a_2296_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2296_);
lean_dec_ref_known(v___x_2273_, 1);
v_a_2264_ = v_a_2296_;
goto v___jp_2263_;
}
v___jp_2263_:
{
if (lean_obj_tag(v_a_2264_) == 11)
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
lean_dec_ref_known(v_a_2264_, 2);
lean_dec_ref(v_file_2261_);
v___x_2265_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__1));
v___x_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
return v___x_2266_;
}
else
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2267_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2268_ = lean_string_append(v_file_2261_, v___x_2267_);
v___x_2269_ = lean_io_error_to_string(v_a_2264_);
v___x_2270_ = lean_string_append(v___x_2268_, v___x_2269_);
lean_dec_ref(v___x_2269_);
v___x_2271_ = lean_mk_io_user_error(v___x_2270_);
v___x_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
return v___x_2272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries___boxed(lean_object* v_file_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lake_Manifest_tryLoadEntries(v_file_2297_);
return v_res_2299_;
}
}
static lean_object* _init_l_Lake_Manifest_saveEntries___closed__0(void){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2300_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__2, &l_Lake_Manifest_toJson___closed__2_once, _init_l_Lake_Manifest_toJson___closed__2);
v___x_2301_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8));
v___x_2302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
lean_ctor_set(v___x_2302_, 1, v___x_2300_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries(lean_object* v_file_2303_, lean_object* v_entries_2304_){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v_contents_2315_; uint32_t v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2306_ = lean_obj_once(&l_Lake_Manifest_saveEntries___closed__0, &l_Lake_Manifest_saveEntries___closed__0_once, _init_l_Lake_Manifest_saveEntries___closed__0);
v___x_2307_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__7));
v___x_2308_ = l_Array_toJson___at___00Lake_Manifest_toJson_spec__0(v_entries_2304_);
v___x_2309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2307_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
v___x_2310_ = lean_box(0);
v___x_2311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2309_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
v___x_2312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2306_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
v___x_2313_ = l_Lean_Json_mkObj(v___x_2312_);
lean_dec_ref_known(v___x_2312_, 2);
v___x_2314_ = lean_unsigned_to_nat(80u);
v_contents_2315_ = l_Lean_Json_pretty(v___x_2313_, v___x_2314_);
v___x_2316_ = 10;
v___x_2317_ = lean_string_push(v_contents_2315_, v___x_2316_);
v___x_2318_ = l_IO_FS_writeFile(v_file_2303_, v___x_2317_);
lean_dec_ref(v___x_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries___boxed(lean_object* v_file_2319_, lean_object* v_entries_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Lake_Manifest_saveEntries(v_file_2319_, v_entries_2320_);
lean_dec_ref(v_file_2319_);
return v_res_2322_;
}
}
lean_object* runtime_initialize_Lake_Util_Version(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Defaults(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin);
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
res = runtime_initialize_Lake_Util_Git(builtin);
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
lean_object* initialize_Lake_Util_Git(uint8_t builtin);
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
res = initialize_Lake_Util_Git(builtin);
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
