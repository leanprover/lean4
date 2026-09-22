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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* l_Lake_JsonObject_getJson_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
extern lean_object* l_Lake_defaultManifestFile;
extern lean_object* l_Lake_defaultConfigFile;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lake_StdVer_compare(lean_object*, lean_object*);
lean_object* l_Lean_Json_getTag_x3f(lean_object*);
lean_object* l_Lean_Json_parseCtorFields(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lake_StdVer_parse(lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_Manifest_version___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(lean_object*);
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
static const lean_ctor_object l_Lake_instInhabitedPackageEntrySrc_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Manifest_version___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_instInhabitedPackageEntrySrc_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedPackageEntrySrc_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedPackageEntrySrc_default = (const lean_object*)&l_Lake_instInhabitedPackageEntrySrc_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedPackageEntrySrc = (const lean_object*)&l_Lake_instInhabitedPackageEntrySrc_default___closed__0_value;
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
static const lean_string_object l_Lake_PackageEntry_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "copy"};
static const lean_object* l_Lake_PackageEntry_toJson___closed__6 = (const lean_object*)&l_Lake_PackageEntry_toJson___closed__6_value;
static const lean_ctor_object l_Lake_PackageEntry_toJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3_value)}};
static const lean_object* l_Lake_PackageEntry_toJson___closed__7 = (const lean_object*)&l_Lake_PackageEntry_toJson___closed__7_value;
static const lean_ctor_object l_Lake_PackageEntry_toJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PackageEntry_toJson___closed__3_value),((lean_object*)&l_Lake_PackageEntry_toJson___closed__7_value)}};
static const lean_object* l_Lake_PackageEntry_toJson___closed__8 = (const lean_object*)&l_Lake_PackageEntry_toJson___closed__8_value;
static const lean_string_object l_Lake_PackageEntry_toJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "inputRev"};
static const lean_object* l_Lake_PackageEntry_toJson___closed__9 = (const lean_object*)&l_Lake_PackageEntry_toJson___closed__9_value;
static const lean_string_object l_Lake_PackageEntry_toJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "subDir"};
static const lean_object* l_Lake_PackageEntry_toJson___closed__10 = (const lean_object*)&l_Lake_PackageEntry_toJson___closed__10_value;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_toJson(lean_object*);
static const lean_closure_object l_Lake_PackageEntry_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageEntry_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageEntry_instToJson___closed__0 = (const lean_object*)&l_Lake_PackageEntry_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_PackageEntry_instToJson = (const lean_object*)&l_Lake_PackageEntry_instToJson___closed__0_value;
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lake_PackageEntry_fromJson_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_PackageEntry_fromJson_x3f_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lake_PackageEntry_fromJson_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_PackageEntry_fromJson_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_PackageEntry_fromJson_x3f_spec__0___boxed(lean_object*);
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
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "copy: "};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__13 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__13_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "manifestFile: "};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__14 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__14_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "property not found: type"};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__15 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__15_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "type: "};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__16 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__16_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "property not found: inherited"};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__17 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__17_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "inherited: "};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__18 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__18_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "configFile: "};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__19 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__19_value;
static const lean_string_object l_Lake_PackageEntry_fromJson_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "scope: "};
static const lean_object* l_Lake_PackageEntry_fromJson_x3f___closed__20 = (const lean_object*)&l_Lake_PackageEntry_fromJson_x3f___closed__20_value;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lake_PackageEntry_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PackageEntry_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PackageEntry_instFromJson___closed__0 = (const lean_object*)&l_Lake_PackageEntry_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_PackageEntry_instFromJson = (const lean_object*)&l_Lake_PackageEntry_instFromJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_prettyName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_dirName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_inputRev_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_inputRev_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setInherited(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setConfigFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setManifestFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_inDirectory(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_addPackage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_Manifest_toJson_spec__0(lean_object*);
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
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "invalid version '"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__0 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__0_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "'; you may need to update your 'lean-toolchain'"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__1 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__1_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "incompatible manifest version '"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__2 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__2_value;
static const lean_ctor_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__3 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__3_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "schema version '"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "' is of a higher major version than this Lake's '"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__5 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__5_value;
static lean_once_cell_t l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "schemaVersion"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7_value;
static const lean_string_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "property not found: schemaVersion"};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8_value;
static const lean_ctor_object l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8_value)}};
static const lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__9 = (const lean_object*)&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1(lean_object*);
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
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(lean_object* v_x_62_){
_start:
{
if (lean_obj_tag(v_x_62_) == 0)
{
lean_object* v___x_63_; 
v___x_63_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0));
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
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(lean_object* v_x_82_){
_start:
{
if (lean_obj_tag(v_x_82_) == 0)
{
lean_object* v___x_83_; 
v___x_83_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0));
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
v___x_312_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(v___x_311_);
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
v___x_324_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v___x_323_);
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
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__1(lean_object* v_x_414_){
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
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(lean_object* v_x_424_){
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
v___x_517_ = lean_nat_add(v___y_514_, v___y_516_);
lean_dec(v___y_516_);
lean_dec(v___y_514_);
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
lean_ctor_set(v___x_496_, 3, v___y_515_);
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
lean_ctor_set(v_reuseFailAlloc_522_, 3, v___y_515_);
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
v___y_514_ = v___x_530_;
v___y_515_ = v___x_529_;
v___y_516_ = v_size_531_;
goto v___jp_513_;
}
else
{
lean_object* v___x_532_; 
v___x_532_ = lean_unsigned_to_nat(0u);
v___y_514_ = v___x_530_;
v___y_515_ = v___x_529_;
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
v___x_905_ = l_Lean_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__1(v_inputRev_x3f_884_);
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__18));
v___x_908_ = l_Lean_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_subDir_x3f_885_);
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
lean_object* v_dir_949_; uint8_t v_copy_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v_dir_949_ = lean_ctor_get(v_t_947_, 0);
lean_inc_ref(v_dir_949_);
v_copy_950_ = lean_ctor_get_uint8(v_t_947_, sizeof(void*)*1);
lean_dec_ref_known(v_t_947_, 1);
v___x_951_ = lean_box(v_copy_950_);
v___x_952_ = lean_apply_2(v_k_948_, v_dir_949_, v___x_951_);
return v___x_952_;
}
else
{
lean_object* v_url_953_; lean_object* v_rev_954_; lean_object* v_inputRev_x3f_955_; lean_object* v_subDir_x3f_956_; lean_object* v___x_957_; 
v_url_953_ = lean_ctor_get(v_t_947_, 0);
lean_inc_ref(v_url_953_);
v_rev_954_ = lean_ctor_get(v_t_947_, 1);
lean_inc_ref(v_rev_954_);
v_inputRev_x3f_955_ = lean_ctor_get(v_t_947_, 2);
lean_inc(v_inputRev_x3f_955_);
v_subDir_x3f_956_ = lean_ctor_get(v_t_947_, 3);
lean_inc(v_subDir_x3f_956_);
lean_dec_ref_known(v_t_947_, 4);
v___x_957_ = lean_apply_4(v_k_948_, v_url_953_, v_rev_954_, v_inputRev_x3f_955_, v_subDir_x3f_956_);
return v___x_957_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorElim(lean_object* v_motive_958_, lean_object* v_ctorIdx_959_, lean_object* v_t_960_, lean_object* v_h_961_, lean_object* v_k_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_960_, v_k_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorElim___boxed(lean_object* v_motive_964_, lean_object* v_ctorIdx_965_, lean_object* v_t_966_, lean_object* v_h_967_, lean_object* v_k_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lake_PackageEntrySrc_ctorElim(v_motive_964_, v_ctorIdx_965_, v_t_966_, v_h_967_, v_k_968_);
lean_dec(v_ctorIdx_965_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_path_elim___redArg(lean_object* v_t_970_, lean_object* v_path_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_970_, v_path_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_path_elim(lean_object* v_motive_973_, lean_object* v_t_974_, lean_object* v_h_975_, lean_object* v_path_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_974_, v_path_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_git_elim___redArg(lean_object* v_t_978_, lean_object* v_git_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_978_, v_git_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_git_elim(lean_object* v_motive_981_, lean_object* v_t_982_, lean_object* v_h_983_, lean_object* v_git_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_982_, v_git_984_);
return v___x_985_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntry_default___closed__0(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_991_ = ((lean_object*)(l_Lake_instInhabitedPackageEntrySrc_default));
v___x_992_ = lean_box(0);
v___x_993_ = l_Lake_defaultConfigFile;
v___x_994_ = 0;
v___x_995_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_996_ = lean_box(0);
v___x_997_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v___x_995_);
lean_ctor_set(v___x_997_, 2, v___x_993_);
lean_ctor_set(v___x_997_, 3, v___x_992_);
lean_ctor_set(v___x_997_, 4, v___x_991_);
lean_ctor_set_uint8(v___x_997_, sizeof(void*)*5, v___x_994_);
return v___x_997_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntry_default(void){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = lean_obj_once(&l_Lake_instInhabitedPackageEntry_default___closed__0, &l_Lake_instInhabitedPackageEntry_default___closed__0_once, _init_l_Lake_instInhabitedPackageEntry_default___closed__0);
return v___x_998_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntry(void){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l_Lake_instInhabitedPackageEntry_default;
return v___x_999_;
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
v___x_1037_ = l_Lean_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_manifestFile_x3f_1022_);
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
lean_object* v_dir_1048_; uint8_t v_copy_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v_dir_1048_ = lean_ctor_get(v_src_1023_, 0);
lean_inc_ref(v_dir_1048_);
v_copy_1049_ = lean_ctor_get_uint8(v_src_1023_, sizeof(void*)*1);
lean_dec_ref_known(v_src_1023_, 1);
v___x_1050_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__5));
v___x_1051_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22));
v___x_1052_ = l_Lake_mkRelPathString(v_dir_1048_);
v___x_1053_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1051_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__6));
v___x_1056_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1056_, 0, v_copy_1049_);
v___x_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v___x_1042_);
v___x_1059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1054_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = l_List_appendTR___redArg(v_fields_1047_, v___x_1059_);
v___x_1061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1050_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = l_Lean_Json_mkObj(v___x_1061_);
lean_dec_ref_known(v___x_1061_, 2);
return v___x_1062_;
}
else
{
lean_object* v_url_1063_; lean_object* v_rev_1064_; lean_object* v_inputRev_x3f_1065_; lean_object* v_subDir_x3f_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v_url_1063_ = lean_ctor_get(v_src_1023_, 0);
lean_inc_ref(v_url_1063_);
v_rev_1064_ = lean_ctor_get(v_src_1023_, 1);
lean_inc_ref(v_rev_1064_);
v_inputRev_x3f_1065_ = lean_ctor_get(v_src_1023_, 2);
lean_inc(v_inputRev_x3f_1065_);
v_subDir_x3f_1066_ = lean_ctor_get(v_src_1023_, 3);
lean_inc(v_subDir_x3f_1066_);
lean_dec_ref_known(v_src_1023_, 4);
v___x_1067_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__8));
v___x_1068_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12));
v___x_1069_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1069_, 0, v_url_1063_);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14));
v___x_1072_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1072_, 0, v_rev_1064_);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__9));
v___x_1075_ = l_Lean_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__1(v_inputRev_x3f_1065_);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__10));
v___x_1078_ = l_Lean_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_subDir_x3f_1066_);
v___x_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
lean_ctor_set(v___x_1080_, 1, v___x_1042_);
v___x_1081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1076_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1073_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1070_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = l_List_appendTR___redArg(v_fields_1047_, v___x_1083_);
v___x_1085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1067_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = l_Lean_Json_mkObj(v___x_1085_);
lean_dec_ref_known(v___x_1085_, 2);
return v___x_1086_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_PackageEntry_fromJson_x3f_spec__0(lean_object* v_x_1091_){
_start:
{
if (lean_obj_tag(v_x_1091_) == 0)
{
lean_object* v___x_1092_; 
v___x_1092_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_PackageEntry_fromJson_x3f_spec__0___closed__0));
return v___x_1092_;
}
else
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_Json_getBool_x3f(v_x_1091_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1093_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1093_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1110_; 
v_a_1102_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1104_ = v___x_1093_;
v_isShared_1105_ = v_isSharedCheck_1110_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1093_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1110_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1106_, 0, v_a_1102_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1106_);
v___x_1108_ = v___x_1104_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_PackageEntry_fromJson_x3f_spec__0___boxed(lean_object* v_x_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_Option_fromJson_x3f___at___00Lake_PackageEntry_fromJson_x3f_spec__0(v_x_1111_);
lean_dec(v_x_1111_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0(lean_object* v_x_1114_){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0));
v___x_1116_ = lean_string_append(v___x_1115_, v_x_1114_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0___boxed(lean_object* v_x_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_x_1117_);
lean_dec_ref(v_x_1117_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f(lean_object* v_json_1140_){
_start:
{
lean_object* v_a_1142_; lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_Json_getObj_x3f(v_json_1140_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1154_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1154_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1154_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1150_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_a_1146_);
lean_dec(v_a_1146_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1150_);
v___x_1152_ = v___x_1148_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
else
{
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
v_a_1155_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1145_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1145_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set_tag(v___x_1157_, 0);
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1404_; 
v_a_1163_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1165_ = v___x_1145_;
v_isShared_1166_ = v_isSharedCheck_1404_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1145_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1404_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_1168_ = l_Lake_JsonObject_getJson_x3f(v_a_1163_, v___x_1167_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v___x_1169_; 
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v___x_1169_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__0));
v_a_1142_ = v___x_1169_;
goto v___jp_1141_;
}
else
{
lean_object* v_val_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1403_; 
v_val_1170_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1172_ = v___x_1168_;
v_isShared_1173_ = v_isSharedCheck_1403_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_val_1170_);
lean_dec(v___x_1168_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1403_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Lean_Name_fromJson_x3f(v_val_1170_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___x_1174_, 1);
v___x_1176_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__1));
v___x_1177_ = lean_string_append(v___x_1176_, v_a_1175_);
lean_dec(v_a_1175_);
v_a_1142_ = v___x_1177_;
goto v___jp_1141_;
}
else
{
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1178_; 
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v_a_1178_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1178_);
lean_dec_ref_known(v___x_1174_, 1);
v_a_1142_ = v_a_1178_;
goto v___jp_1141_;
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1402_; 
v_a_1179_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1181_ = v___x_1174_;
v_isShared_1182_ = v_isSharedCheck_1402_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1174_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1402_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v_a_1184_; lean_object* v___y_1196_; uint8_t v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v_a_1200_; lean_object* v___y_1209_; lean_object* v___y_1210_; uint8_t v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v_a_1216_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; uint8_t v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v_a_1225_; lean_object* v___y_1237_; lean_object* v___y_1238_; uint8_t v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; uint8_t v_a_1242_; lean_object* v___y_1245_; lean_object* v___y_1246_; uint8_t v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; uint8_t v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v_a_1256_; uint8_t v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; uint8_t v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v_a_1325_; uint8_t v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v_a_1342_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__0));
v___x_1379_ = l_Lake_JsonObject_getJson_x3f(v_a_1163_, v___x_1378_);
if (lean_obj_tag(v___x_1379_) == 0)
{
goto v___jp_1376_;
}
else
{
lean_object* v_val_1380_; lean_object* v___x_1381_; 
v_val_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_val_1380_);
lean_dec_ref_known(v___x_1379_, 1);
v___x_1381_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(v_val_1380_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1391_; 
lean_del_object(v___x_1181_);
lean_dec(v_a_1179_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1384_ = v___x_1381_;
v_isShared_1385_ = v_isSharedCheck_1391_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1381_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1391_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1386_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__20));
v___x_1387_ = lean_string_append(v___x_1386_, v_a_1382_);
lean_dec(v_a_1382_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v___x_1387_);
v___x_1389_ = v___x_1384_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
else
{
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
lean_del_object(v___x_1181_);
lean_dec(v_a_1179_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v_a_1392_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1381_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1381_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set_tag(v___x_1394_, 0);
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
else
{
lean_object* v_a_1400_; 
v_a_1400_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1400_);
lean_dec_ref_known(v___x_1381_, 1);
if (lean_obj_tag(v_a_1400_) == 0)
{
goto v___jp_1376_;
}
else
{
lean_object* v_val_1401_; 
v_val_1401_ = lean_ctor_get(v_a_1400_, 0);
lean_inc(v_val_1401_);
lean_dec_ref_known(v_a_1400_, 1);
v_a_1342_ = v_val_1401_;
goto v___jp_1341_;
}
}
}
}
v___jp_1183_:
{
lean_object* v___x_1185_; uint8_t v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1185_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__2));
v___x_1186_ = 1;
v___x_1187_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_1179_, v___x_1186_);
v___x_1188_ = lean_string_append(v___x_1185_, v___x_1187_);
lean_dec_ref(v___x_1187_);
v___x_1189_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__3));
v___x_1190_ = lean_string_append(v___x_1188_, v___x_1189_);
v___x_1191_ = lean_string_append(v___x_1190_, v_a_1184_);
lean_dec_ref(v_a_1184_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set_tag(v___x_1181_, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1191_);
v___x_1193_ = v___x_1181_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
v___jp_1195_:
{
lean_object* v___x_1202_; 
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 0, v___y_1196_);
v___x_1202_ = v___x_1172_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___y_1196_);
v___x_1202_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1203_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1203_, 0, v_a_1179_);
lean_ctor_set(v___x_1203_, 1, v___y_1199_);
lean_ctor_set(v___x_1203_, 2, v___y_1198_);
lean_ctor_set(v___x_1203_, 3, v___x_1202_);
lean_ctor_set(v___x_1203_, 4, v_a_1200_);
lean_ctor_set_uint8(v___x_1203_, sizeof(void*)*5, v___y_1197_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1203_);
v___x_1205_ = v___x_1165_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
v___jp_1208_:
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1217_, 0, v___y_1213_);
lean_ctor_set(v___x_1217_, 1, v___y_1210_);
lean_ctor_set(v___x_1217_, 2, v___y_1212_);
lean_ctor_set(v___x_1217_, 3, v_a_1216_);
v___y_1196_ = v___y_1209_;
v___y_1197_ = v___y_1211_;
v___y_1198_ = v___y_1214_;
v___y_1199_ = v___y_1215_;
v_a_1200_ = v___x_1217_;
goto v___jp_1195_;
}
v___jp_1218_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__10));
v___x_1227_ = l_Lake_JsonObject_getJson_x3f(v_a_1163_, v___x_1226_);
lean_dec(v_a_1163_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v___x_1228_; 
lean_del_object(v___x_1181_);
v___x_1228_ = lean_box(0);
v___y_1209_ = v___y_1219_;
v___y_1210_ = v___y_1220_;
v___y_1211_ = v___y_1222_;
v___y_1212_ = v_a_1225_;
v___y_1213_ = v___y_1221_;
v___y_1214_ = v___y_1223_;
v___y_1215_ = v___y_1224_;
v_a_1216_ = v___x_1228_;
goto v___jp_1208_;
}
else
{
lean_object* v_val_1229_; lean_object* v___x_1230_; 
v_val_1229_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_val_1229_);
lean_dec_ref_known(v___x_1227_, 1);
v___x_1230_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1229_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_dec(v_a_1225_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1231_);
lean_dec_ref_known(v___x_1230_, 1);
v___x_1232_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__4));
v___x_1233_ = lean_string_append(v___x_1232_, v_a_1231_);
lean_dec(v_a_1231_);
v_a_1184_ = v___x_1233_;
goto v___jp_1183_;
}
else
{
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1234_; 
lean_dec(v_a_1225_);
lean_dec_ref(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
v_a_1234_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1234_);
lean_dec_ref_known(v___x_1230_, 1);
v_a_1184_ = v_a_1234_;
goto v___jp_1183_;
}
else
{
lean_object* v_a_1235_; 
lean_del_object(v___x_1181_);
v_a_1235_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1230_, 1);
v___y_1209_ = v___y_1219_;
v___y_1210_ = v___y_1220_;
v___y_1211_ = v___y_1222_;
v___y_1212_ = v_a_1225_;
v___y_1213_ = v___y_1221_;
v___y_1214_ = v___y_1223_;
v___y_1215_ = v___y_1224_;
v_a_1216_ = v_a_1235_;
goto v___jp_1208_;
}
}
}
}
v___jp_1236_:
{
lean_object* v___x_1243_; 
v___x_1243_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1243_, 0, v___y_1238_);
lean_ctor_set_uint8(v___x_1243_, sizeof(void*)*1, v_a_1242_);
v___y_1196_ = v___y_1237_;
v___y_1197_ = v___y_1239_;
v___y_1198_ = v___y_1240_;
v___y_1199_ = v___y_1241_;
v_a_1200_ = v___x_1243_;
goto v___jp_1195_;
}
v___jp_1244_:
{
uint8_t v___x_1250_; 
v___x_1250_ = 0;
v___y_1237_ = v___y_1245_;
v___y_1238_ = v___y_1246_;
v___y_1239_ = v___y_1247_;
v___y_1240_ = v___y_1248_;
v___y_1241_ = v___y_1249_;
v_a_1242_ = v___x_1250_;
goto v___jp_1236_;
}
v___jp_1251_:
{
lean_object* v___x_1257_; uint8_t v___x_1258_; 
v___x_1257_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2));
v___x_1258_ = lean_string_dec_eq(v___y_1253_, v___x_1257_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; uint8_t v___x_1260_; 
v___x_1259_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3));
v___x_1260_ = lean_string_dec_eq(v___y_1253_, v___x_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_dec_ref(v_a_1256_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v___x_1261_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__5));
v___x_1262_ = lean_string_append(v___x_1261_, v___y_1253_);
lean_dec_ref(v___y_1253_);
v___x_1263_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1264_ = lean_string_append(v___x_1262_, v___x_1263_);
v_a_1184_ = v___x_1264_;
goto v___jp_1183_;
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_dec_ref(v___y_1253_);
v___x_1265_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12));
v___x_1266_ = l_Lake_JsonObject_getJson_x3f(v_a_1163_, v___x_1265_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v___x_1267_; 
lean_dec_ref(v_a_1256_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v___x_1267_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__6));
v_a_1184_ = v___x_1267_;
goto v___jp_1183_;
}
else
{
lean_object* v_val_1268_; lean_object* v___x_1269_; 
v_val_1268_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_val_1268_);
lean_dec_ref_known(v___x_1266_, 1);
v___x_1269_ = l_Lean_Json_getStr_x3f(v_val_1268_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
lean_dec_ref(v_a_1256_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1269_, 1);
v___x_1271_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__7));
v___x_1272_ = lean_string_append(v___x_1271_, v_a_1270_);
lean_dec(v_a_1270_);
v_a_1184_ = v___x_1272_;
goto v___jp_1183_;
}
else
{
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1273_; 
lean_dec_ref(v_a_1256_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v_a_1273_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___x_1269_, 1);
v_a_1184_ = v_a_1273_;
goto v___jp_1183_;
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v_a_1274_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1274_);
lean_dec_ref_known(v___x_1269_, 1);
v___x_1275_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14));
v___x_1276_ = l_Lake_JsonObject_getJson_x3f(v_a_1163_, v___x_1275_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v___x_1277_; 
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1256_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v___x_1277_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__8));
v_a_1184_ = v___x_1277_;
goto v___jp_1183_;
}
else
{
lean_object* v_val_1278_; lean_object* v___x_1279_; 
v_val_1278_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_val_1278_);
lean_dec_ref_known(v___x_1276_, 1);
v___x_1279_ = l_Lean_Json_getStr_x3f(v_val_1278_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1256_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v___x_1281_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__9));
v___x_1282_ = lean_string_append(v___x_1281_, v_a_1280_);
lean_dec(v_a_1280_);
v_a_1184_ = v___x_1282_;
goto v___jp_1183_;
}
else
{
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1283_; 
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1256_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v_a_1283_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1283_);
lean_dec_ref_known(v___x_1279_, 1);
v_a_1184_ = v_a_1283_;
goto v___jp_1183_;
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v_a_1284_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1279_, 1);
v___x_1285_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__9));
v___x_1286_ = l_Lake_JsonObject_getJson_x3f(v_a_1163_, v___x_1285_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v___x_1287_; 
v___x_1287_ = lean_box(0);
v___y_1219_ = v_a_1256_;
v___y_1220_ = v_a_1284_;
v___y_1221_ = v_a_1274_;
v___y_1222_ = v___y_1252_;
v___y_1223_ = v___y_1254_;
v___y_1224_ = v___y_1255_;
v_a_1225_ = v___x_1287_;
goto v___jp_1218_;
}
else
{
lean_object* v_val_1288_; lean_object* v___x_1289_; 
v_val_1288_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_val_1288_);
lean_dec_ref_known(v___x_1286_, 1);
v___x_1289_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(v_val_1288_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
lean_dec(v_a_1284_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1256_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1290_);
lean_dec_ref_known(v___x_1289_, 1);
v___x_1291_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__10));
v___x_1292_ = lean_string_append(v___x_1291_, v_a_1290_);
lean_dec(v_a_1290_);
v_a_1184_ = v___x_1292_;
goto v___jp_1183_;
}
else
{
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1293_; 
lean_dec(v_a_1284_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1256_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v_a_1293_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1293_);
lean_dec_ref_known(v___x_1289_, 1);
v_a_1184_ = v_a_1293_;
goto v___jp_1183_;
}
else
{
lean_object* v_a_1294_; 
v_a_1294_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1294_);
lean_dec_ref_known(v___x_1289_, 1);
v___y_1219_ = v_a_1256_;
v___y_1220_ = v_a_1284_;
v___y_1221_ = v_a_1274_;
v___y_1222_ = v___y_1252_;
v___y_1223_ = v___y_1254_;
v___y_1224_ = v___y_1255_;
v_a_1225_ = v_a_1294_;
goto v___jp_1218_;
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
lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_dec_ref(v___y_1253_);
v___x_1295_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22));
v___x_1296_ = l_Lake_JsonObject_getJson_x3f(v_a_1163_, v___x_1295_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v___x_1297_; 
lean_dec_ref(v_a_1256_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v___x_1297_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__11));
v_a_1184_ = v___x_1297_;
goto v___jp_1183_;
}
else
{
lean_object* v_val_1298_; lean_object* v___x_1299_; 
v_val_1298_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_val_1298_);
lean_dec_ref_known(v___x_1296_, 1);
v___x_1299_ = l_Lean_Json_getStr_x3f(v_val_1298_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
lean_dec_ref(v_a_1256_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
lean_dec_ref_known(v___x_1299_, 1);
v___x_1301_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__12));
v___x_1302_ = lean_string_append(v___x_1301_, v_a_1300_);
lean_dec(v_a_1300_);
v_a_1184_ = v___x_1302_;
goto v___jp_1183_;
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v_a_1303_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1303_);
lean_dec_ref_known(v___x_1299_, 1);
v___x_1304_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__6));
v___x_1305_ = l_Lake_JsonObject_getJson_x3f(v_a_1163_, v___x_1304_);
lean_dec(v_a_1163_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_del_object(v___x_1181_);
v___y_1245_ = v_a_1256_;
v___y_1246_ = v_a_1303_;
v___y_1247_ = v___y_1252_;
v___y_1248_ = v___y_1254_;
v___y_1249_ = v___y_1255_;
goto v___jp_1244_;
}
else
{
lean_object* v_val_1306_; lean_object* v___x_1307_; 
v_val_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_val_1306_);
lean_dec_ref_known(v___x_1305_, 1);
v___x_1307_ = l_Lean_Option_fromJson_x3f___at___00Lake_PackageEntry_fromJson_x3f_spec__0(v_val_1306_);
lean_dec(v_val_1306_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1256_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1308_);
lean_dec_ref_known(v___x_1307_, 1);
v___x_1309_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__13));
v___x_1310_ = lean_string_append(v___x_1309_, v_a_1308_);
lean_dec(v_a_1308_);
v_a_1184_ = v___x_1310_;
goto v___jp_1183_;
}
else
{
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1311_; 
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1256_);
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
v_a_1311_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1311_);
lean_dec_ref_known(v___x_1307_, 1);
v_a_1184_ = v_a_1311_;
goto v___jp_1183_;
}
else
{
lean_object* v_a_1312_; 
lean_del_object(v___x_1181_);
v_a_1312_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1312_);
lean_dec_ref_known(v___x_1307_, 1);
if (lean_obj_tag(v_a_1312_) == 0)
{
v___y_1245_ = v_a_1256_;
v___y_1246_ = v_a_1303_;
v___y_1247_ = v___y_1252_;
v___y_1248_ = v___y_1254_;
v___y_1249_ = v___y_1255_;
goto v___jp_1244_;
}
else
{
lean_object* v_val_1313_; uint8_t v___x_1314_; 
v_val_1313_ = lean_ctor_get(v_a_1312_, 0);
lean_inc(v_val_1313_);
lean_dec_ref_known(v_a_1312_, 1);
v___x_1314_ = lean_unbox(v_val_1313_);
lean_dec(v_val_1313_);
v___y_1237_ = v_a_1256_;
v___y_1238_ = v_a_1303_;
v___y_1239_ = v___y_1252_;
v___y_1240_ = v___y_1254_;
v___y_1241_ = v___y_1255_;
v_a_1242_ = v___x_1314_;
goto v___jp_1236_;
}
}
}
}
}
}
}
}
v___jp_1315_:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lake_defaultManifestFile;
v___y_1252_ = v___y_1316_;
v___y_1253_ = v___y_1317_;
v___y_1254_ = v___y_1318_;
v___y_1255_ = v___y_1319_;
v_a_1256_ = v___x_1320_;
goto v___jp_1251_;
}
v___jp_1321_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__2));
v___x_1327_ = l_Lake_JsonObject_getJson_x3f(v_a_1163_, v___x_1326_);
if (lean_obj_tag(v___x_1327_) == 0)
{
v___y_1316_ = v___y_1322_;
v___y_1317_ = v___y_1323_;
v___y_1318_ = v_a_1325_;
v___y_1319_ = v___y_1324_;
goto v___jp_1315_;
}
else
{
lean_object* v_val_1328_; lean_object* v___x_1329_; 
v_val_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_val_1328_);
lean_dec_ref_known(v___x_1327_, 1);
v___x_1329_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1328_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_dec_ref(v_a_1325_);
lean_dec_ref(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1330_);
lean_dec_ref_known(v___x_1329_, 1);
v___x_1331_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__14));
v___x_1332_ = lean_string_append(v___x_1331_, v_a_1330_);
lean_dec(v_a_1330_);
v_a_1184_ = v___x_1332_;
goto v___jp_1183_;
}
else
{
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1333_; 
lean_dec_ref(v_a_1325_);
lean_dec_ref(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v_a_1333_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1333_);
lean_dec_ref_known(v___x_1329_, 1);
v_a_1184_ = v_a_1333_;
goto v___jp_1183_;
}
else
{
lean_object* v_a_1334_; 
v_a_1334_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1334_);
lean_dec_ref_known(v___x_1329_, 1);
if (lean_obj_tag(v_a_1334_) == 0)
{
v___y_1316_ = v___y_1322_;
v___y_1317_ = v___y_1323_;
v___y_1318_ = v_a_1325_;
v___y_1319_ = v___y_1324_;
goto v___jp_1315_;
}
else
{
lean_object* v_val_1335_; 
v_val_1335_ = lean_ctor_get(v_a_1334_, 0);
lean_inc(v_val_1335_);
lean_dec_ref_known(v_a_1334_, 1);
v___y_1252_ = v___y_1322_;
v___y_1253_ = v___y_1323_;
v___y_1254_ = v_a_1325_;
v___y_1255_ = v___y_1324_;
v_a_1256_ = v_val_1335_;
goto v___jp_1251_;
}
}
}
}
}
v___jp_1336_:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lake_defaultConfigFile;
v___y_1322_ = v___y_1337_;
v___y_1323_ = v___y_1338_;
v___y_1324_ = v___y_1339_;
v_a_1325_ = v___x_1340_;
goto v___jp_1321_;
}
v___jp_1341_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__3));
v___x_1344_ = l_Lake_JsonObject_getJson_x3f(v_a_1163_, v___x_1343_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v___x_1345_; 
lean_dec_ref(v_a_1342_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v___x_1345_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__15));
v_a_1184_ = v___x_1345_;
goto v___jp_1183_;
}
else
{
lean_object* v_val_1346_; lean_object* v___x_1347_; 
v_val_1346_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_val_1346_);
lean_dec_ref_known(v___x_1344_, 1);
v___x_1347_ = l_Lean_Json_getStr_x3f(v_val_1346_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec_ref(v_a_1342_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1347_, 1);
v___x_1349_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__16));
v___x_1350_ = lean_string_append(v___x_1349_, v_a_1348_);
lean_dec(v_a_1348_);
v_a_1184_ = v___x_1350_;
goto v___jp_1183_;
}
else
{
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1351_; 
lean_dec_ref(v_a_1342_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v_a_1351_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1347_, 1);
v_a_1184_ = v_a_1351_;
goto v___jp_1183_;
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v_a_1352_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1347_, 1);
v___x_1353_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10));
v___x_1354_ = l_Lake_JsonObject_getJson_x3f(v_a_1163_, v___x_1353_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v___x_1355_; 
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1342_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v___x_1355_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__17));
v_a_1184_ = v___x_1355_;
goto v___jp_1183_;
}
else
{
lean_object* v_val_1356_; lean_object* v___x_1357_; 
v_val_1356_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_val_1356_);
lean_dec_ref_known(v___x_1354_, 1);
v___x_1357_ = l_Lean_Json_getBool_x3f(v_val_1356_);
lean_dec(v_val_1356_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1342_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v___x_1357_, 1);
v___x_1359_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__18));
v___x_1360_ = lean_string_append(v___x_1359_, v_a_1358_);
lean_dec(v_a_1358_);
v_a_1184_ = v___x_1360_;
goto v___jp_1183_;
}
else
{
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1361_; 
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1342_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v_a_1361_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1361_);
lean_dec_ref_known(v___x_1357_, 1);
v_a_1184_ = v_a_1361_;
goto v___jp_1183_;
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v_a_1362_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1362_);
lean_dec_ref_known(v___x_1357_, 1);
v___x_1363_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__1));
v___x_1364_ = l_Lake_JsonObject_getJson_x3f(v_a_1163_, v___x_1363_);
if (lean_obj_tag(v___x_1364_) == 0)
{
uint8_t v___x_1365_; 
v___x_1365_ = lean_unbox(v_a_1362_);
lean_dec(v_a_1362_);
v___y_1337_ = v___x_1365_;
v___y_1338_ = v_a_1352_;
v___y_1339_ = v_a_1342_;
goto v___jp_1336_;
}
else
{
lean_object* v_val_1366_; lean_object* v___x_1367_; 
v_val_1366_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_val_1366_);
lean_dec_ref_known(v___x_1364_, 1);
v___x_1367_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1366_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
lean_dec(v_a_1362_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1342_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1368_);
lean_dec_ref_known(v___x_1367_, 1);
v___x_1369_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__19));
v___x_1370_ = lean_string_append(v___x_1369_, v_a_1368_);
lean_dec(v_a_1368_);
v_a_1184_ = v___x_1370_;
goto v___jp_1183_;
}
else
{
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1371_; 
lean_dec(v_a_1362_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1342_);
lean_del_object(v___x_1172_);
lean_del_object(v___x_1165_);
lean_dec(v_a_1163_);
v_a_1371_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1371_);
lean_dec_ref_known(v___x_1367_, 1);
v_a_1184_ = v_a_1371_;
goto v___jp_1183_;
}
else
{
lean_object* v_a_1372_; 
v_a_1372_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1372_);
lean_dec_ref_known(v___x_1367_, 1);
if (lean_obj_tag(v_a_1372_) == 0)
{
uint8_t v___x_1373_; 
v___x_1373_ = lean_unbox(v_a_1362_);
lean_dec(v_a_1362_);
v___y_1337_ = v___x_1373_;
v___y_1338_ = v_a_1352_;
v___y_1339_ = v_a_1342_;
goto v___jp_1336_;
}
else
{
lean_object* v_val_1374_; uint8_t v___x_1375_; 
v_val_1374_ = lean_ctor_get(v_a_1372_, 0);
lean_inc(v_val_1374_);
lean_dec_ref_known(v_a_1372_, 1);
v___x_1375_ = lean_unbox(v_a_1362_);
lean_dec(v_a_1362_);
v___y_1322_ = v___x_1375_;
v___y_1323_ = v_a_1352_;
v___y_1324_ = v_a_1342_;
v_a_1325_ = v_val_1374_;
goto v___jp_1321_;
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
v___jp_1376_:
{
lean_object* v___x_1377_; 
v___x_1377_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v_a_1342_ = v___x_1377_;
goto v___jp_1341_;
}
}
}
}
}
}
}
}
}
v___jp_1141_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_a_1142_);
lean_dec_ref(v_a_1142_);
v___x_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_prettyName(lean_object* v_entry_1407_){
_start:
{
lean_object* v_name_1408_; uint8_t v___x_1409_; lean_object* v___x_1410_; 
v_name_1408_ = lean_ctor_get(v_entry_1407_, 0);
lean_inc(v_name_1408_);
lean_dec_ref(v_entry_1407_);
v___x_1409_ = 0;
v___x_1410_ = l_Lean_Name_toString(v_name_1408_, v___x_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_dirName(lean_object* v_entry_1411_){
_start:
{
lean_object* v_name_1412_; uint8_t v___x_1413_; lean_object* v___x_1414_; 
v_name_1412_ = lean_ctor_get(v_entry_1411_, 0);
lean_inc(v_name_1412_);
lean_dec_ref(v_entry_1411_);
v___x_1413_ = 0;
v___x_1414_ = l_Lean_Name_toString(v_name_1412_, v___x_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_inputRev_x3f(lean_object* v_entry_1415_){
_start:
{
lean_object* v_src_1416_; 
v_src_1416_ = lean_ctor_get(v_entry_1415_, 4);
if (lean_obj_tag(v_src_1416_) == 0)
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_box(0);
return v___x_1417_;
}
else
{
lean_object* v_inputRev_x3f_1418_; 
v_inputRev_x3f_1418_ = lean_ctor_get(v_src_1416_, 2);
lean_inc(v_inputRev_x3f_1418_);
return v_inputRev_x3f_1418_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_inputRev_x3f___boxed(lean_object* v_entry_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Lake_PackageEntry_inputRev_x3f(v_entry_1419_);
lean_dec_ref(v_entry_1419_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setInherited(lean_object* v_entry_1421_){
_start:
{
lean_object* v_name_1422_; lean_object* v_scope_1423_; lean_object* v_configFile_1424_; lean_object* v_manifestFile_x3f_1425_; lean_object* v_src_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1434_; 
v_name_1422_ = lean_ctor_get(v_entry_1421_, 0);
v_scope_1423_ = lean_ctor_get(v_entry_1421_, 1);
v_configFile_1424_ = lean_ctor_get(v_entry_1421_, 2);
v_manifestFile_x3f_1425_ = lean_ctor_get(v_entry_1421_, 3);
v_src_1426_ = lean_ctor_get(v_entry_1421_, 4);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_entry_1421_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1428_ = v_entry_1421_;
v_isShared_1429_ = v_isSharedCheck_1434_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_src_1426_);
lean_inc(v_manifestFile_x3f_1425_);
lean_inc(v_configFile_1424_);
lean_inc(v_scope_1423_);
lean_inc(v_name_1422_);
lean_dec(v_entry_1421_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1434_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
uint8_t v___x_1430_; lean_object* v___x_1432_; 
v___x_1430_ = 1;
if (v_isShared_1429_ == 0)
{
v___x_1432_ = v___x_1428_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_name_1422_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_scope_1423_);
lean_ctor_set(v_reuseFailAlloc_1433_, 2, v_configFile_1424_);
lean_ctor_set(v_reuseFailAlloc_1433_, 3, v_manifestFile_x3f_1425_);
lean_ctor_set(v_reuseFailAlloc_1433_, 4, v_src_1426_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_ctor_set_uint8(v___x_1432_, sizeof(void*)*5, v___x_1430_);
return v___x_1432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setConfigFile(lean_object* v_path_1435_, lean_object* v_entry_1436_){
_start:
{
lean_object* v_name_1437_; lean_object* v_scope_1438_; uint8_t v_inherited_1439_; lean_object* v_manifestFile_x3f_1440_; lean_object* v_src_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
v_name_1437_ = lean_ctor_get(v_entry_1436_, 0);
v_scope_1438_ = lean_ctor_get(v_entry_1436_, 1);
v_inherited_1439_ = lean_ctor_get_uint8(v_entry_1436_, sizeof(void*)*5);
v_manifestFile_x3f_1440_ = lean_ctor_get(v_entry_1436_, 3);
v_src_1441_ = lean_ctor_get(v_entry_1436_, 4);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_entry_1436_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; 
v_unused_1449_ = lean_ctor_get(v_entry_1436_, 2);
lean_dec(v_unused_1449_);
v___x_1443_ = v_entry_1436_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_src_1441_);
lean_inc(v_manifestFile_x3f_1440_);
lean_inc(v_scope_1438_);
lean_inc(v_name_1437_);
lean_dec(v_entry_1436_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 2, v_path_1435_);
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_name_1437_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_scope_1438_);
lean_ctor_set(v_reuseFailAlloc_1447_, 2, v_path_1435_);
lean_ctor_set(v_reuseFailAlloc_1447_, 3, v_manifestFile_x3f_1440_);
lean_ctor_set(v_reuseFailAlloc_1447_, 4, v_src_1441_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, sizeof(void*)*5, v_inherited_1439_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setManifestFile(lean_object* v_path_x3f_1450_, lean_object* v_entry_1451_){
_start:
{
lean_object* v_name_1452_; lean_object* v_scope_1453_; uint8_t v_inherited_1454_; lean_object* v_configFile_1455_; lean_object* v_src_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
v_name_1452_ = lean_ctor_get(v_entry_1451_, 0);
v_scope_1453_ = lean_ctor_get(v_entry_1451_, 1);
v_inherited_1454_ = lean_ctor_get_uint8(v_entry_1451_, sizeof(void*)*5);
v_configFile_1455_ = lean_ctor_get(v_entry_1451_, 2);
v_src_1456_ = lean_ctor_get(v_entry_1451_, 4);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_entry_1451_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v_entry_1451_, 3);
lean_dec(v_unused_1464_);
v___x_1458_ = v_entry_1451_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_src_1456_);
lean_inc(v_configFile_1455_);
lean_inc(v_scope_1453_);
lean_inc(v_name_1452_);
lean_dec(v_entry_1451_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 3, v_path_x3f_1450_);
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_name_1452_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_scope_1453_);
lean_ctor_set(v_reuseFailAlloc_1462_, 2, v_configFile_1455_);
lean_ctor_set(v_reuseFailAlloc_1462_, 3, v_path_x3f_1450_);
lean_ctor_set(v_reuseFailAlloc_1462_, 4, v_src_1456_);
lean_ctor_set_uint8(v_reuseFailAlloc_1462_, sizeof(void*)*5, v_inherited_1454_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_inDirectory(lean_object* v_pkgDir_1465_, lean_object* v_entry_1466_){
_start:
{
lean_object* v_src_1467_; 
v_src_1467_ = lean_ctor_get(v_entry_1466_, 4);
lean_inc_ref(v_src_1467_);
if (lean_obj_tag(v_src_1467_) == 0)
{
uint8_t v_copy_1468_; 
v_copy_1468_ = lean_ctor_get_uint8(v_src_1467_, sizeof(void*)*1);
if (v_copy_1468_ == 0)
{
lean_object* v_name_1469_; lean_object* v_scope_1470_; uint8_t v_inherited_1471_; lean_object* v_configFile_1472_; lean_object* v_manifestFile_x3f_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1489_; 
v_name_1469_ = lean_ctor_get(v_entry_1466_, 0);
v_scope_1470_ = lean_ctor_get(v_entry_1466_, 1);
v_inherited_1471_ = lean_ctor_get_uint8(v_entry_1466_, sizeof(void*)*5);
v_configFile_1472_ = lean_ctor_get(v_entry_1466_, 2);
v_manifestFile_x3f_1473_ = lean_ctor_get(v_entry_1466_, 3);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_entry_1466_);
if (v_isSharedCheck_1489_ == 0)
{
lean_object* v_unused_1490_; 
v_unused_1490_ = lean_ctor_get(v_entry_1466_, 4);
lean_dec(v_unused_1490_);
v___x_1475_ = v_entry_1466_;
v_isShared_1476_ = v_isSharedCheck_1489_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_manifestFile_x3f_1473_);
lean_inc(v_configFile_1472_);
lean_inc(v_scope_1470_);
lean_inc(v_name_1469_);
lean_dec(v_entry_1466_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1489_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v_dir_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1488_; 
v_dir_1477_ = lean_ctor_get(v_src_1467_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_src_1467_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1479_ = v_src_1467_;
v_isShared_1480_ = v_isSharedCheck_1488_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_dir_1477_);
lean_dec(v_src_1467_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1488_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1481_; lean_object* v___x_1483_; 
v___x_1481_ = l_Lake_joinRelative(v_pkgDir_1465_, v_dir_1477_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 0, v___x_1481_);
v___x_1483_ = v___x_1479_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1481_);
lean_ctor_set_uint8(v_reuseFailAlloc_1487_, sizeof(void*)*1, v_copy_1468_);
v___x_1483_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1485_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 4, v___x_1483_);
v___x_1485_ = v___x_1475_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_name_1469_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_scope_1470_);
lean_ctor_set(v_reuseFailAlloc_1486_, 2, v_configFile_1472_);
lean_ctor_set(v_reuseFailAlloc_1486_, 3, v_manifestFile_x3f_1473_);
lean_ctor_set(v_reuseFailAlloc_1486_, 4, v___x_1483_);
lean_ctor_set_uint8(v_reuseFailAlloc_1486_, sizeof(void*)*5, v_inherited_1471_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_src_1467_, 1);
lean_dec_ref(v_pkgDir_1465_);
return v_entry_1466_;
}
}
else
{
lean_dec_ref(v_src_1467_);
lean_dec_ref(v_pkgDir_1465_);
return v_entry_1466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(lean_object* v_x_1491_){
_start:
{
if (lean_obj_tag(v_x_1491_) == 0)
{
lean_object* v_name_1492_; uint8_t v_inherited_1493_; lean_object* v_dir_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v_name_1492_ = lean_ctor_get(v_x_1491_, 0);
v_inherited_1493_ = lean_ctor_get_uint8(v_x_1491_, sizeof(void*)*3);
v_dir_1494_ = lean_ctor_get(v_x_1491_, 2);
v___x_1495_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_1496_ = l_Lake_defaultConfigFile;
v___x_1497_ = lean_box(0);
v___x_1498_ = 0;
lean_inc_ref(v_dir_1494_);
v___x_1499_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1499_, 0, v_dir_1494_);
lean_ctor_set_uint8(v___x_1499_, sizeof(void*)*1, v___x_1498_);
lean_inc(v_name_1492_);
v___x_1500_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1500_, 0, v_name_1492_);
lean_ctor_set(v___x_1500_, 1, v___x_1495_);
lean_ctor_set(v___x_1500_, 2, v___x_1496_);
lean_ctor_set(v___x_1500_, 3, v___x_1497_);
lean_ctor_set(v___x_1500_, 4, v___x_1499_);
lean_ctor_set_uint8(v___x_1500_, sizeof(void*)*5, v_inherited_1493_);
return v___x_1500_;
}
else
{
lean_object* v_name_1501_; uint8_t v_inherited_1502_; lean_object* v_url_1503_; lean_object* v_rev_1504_; lean_object* v_inputRev_x3f_1505_; lean_object* v_subDir_x3f_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v_name_1501_ = lean_ctor_get(v_x_1491_, 0);
v_inherited_1502_ = lean_ctor_get_uint8(v_x_1491_, sizeof(void*)*6);
v_url_1503_ = lean_ctor_get(v_x_1491_, 2);
v_rev_1504_ = lean_ctor_get(v_x_1491_, 3);
v_inputRev_x3f_1505_ = lean_ctor_get(v_x_1491_, 4);
v_subDir_x3f_1506_ = lean_ctor_get(v_x_1491_, 5);
v___x_1507_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_1508_ = l_Lake_defaultConfigFile;
v___x_1509_ = lean_box(0);
lean_inc(v_subDir_x3f_1506_);
lean_inc(v_inputRev_x3f_1505_);
lean_inc_ref(v_rev_1504_);
lean_inc_ref(v_url_1503_);
v___x_1510_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1510_, 0, v_url_1503_);
lean_ctor_set(v___x_1510_, 1, v_rev_1504_);
lean_ctor_set(v___x_1510_, 2, v_inputRev_x3f_1505_);
lean_ctor_set(v___x_1510_, 3, v_subDir_x3f_1506_);
lean_inc(v_name_1501_);
v___x_1511_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1511_, 0, v_name_1501_);
lean_ctor_set(v___x_1511_, 1, v___x_1507_);
lean_ctor_set(v___x_1511_, 2, v___x_1508_);
lean_ctor_set(v___x_1511_, 3, v___x_1509_);
lean_ctor_set(v___x_1511_, 4, v___x_1510_);
lean_ctor_set_uint8(v___x_1511_, sizeof(void*)*5, v_inherited_1502_);
return v___x_1511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6___boxed(lean_object* v_x_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(v_x_1512_);
lean_dec_ref(v_x_1512_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_addPackage(lean_object* v_entry_1514_, lean_object* v_self_1515_){
_start:
{
lean_object* v_name_1516_; lean_object* v_lakeDir_1517_; uint8_t v_fixedToolchain_1518_; lean_object* v_packagesDir_x3f_1519_; lean_object* v_packages_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1528_; 
v_name_1516_ = lean_ctor_get(v_self_1515_, 0);
v_lakeDir_1517_ = lean_ctor_get(v_self_1515_, 1);
v_fixedToolchain_1518_ = lean_ctor_get_uint8(v_self_1515_, sizeof(void*)*4);
v_packagesDir_x3f_1519_ = lean_ctor_get(v_self_1515_, 2);
v_packages_1520_ = lean_ctor_get(v_self_1515_, 3);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_self_1515_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1522_ = v_self_1515_;
v_isShared_1523_ = v_isSharedCheck_1528_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_packages_1520_);
lean_inc(v_packagesDir_x3f_1519_);
lean_inc(v_lakeDir_1517_);
lean_inc(v_name_1516_);
lean_dec(v_self_1515_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1528_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1524_ = lean_array_push(v_packages_1520_, v_entry_1514_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 3, v___x_1524_);
v___x_1526_ = v___x_1522_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_name_1516_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_lakeDir_1517_);
lean_ctor_set(v_reuseFailAlloc_1527_, 2, v_packagesDir_x3f_1519_);
lean_ctor_set(v_reuseFailAlloc_1527_, 3, v___x_1524_);
lean_ctor_set_uint8(v_reuseFailAlloc_1527_, sizeof(void*)*4, v_fixedToolchain_1518_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(size_t v_sz_1529_, size_t v_i_1530_, lean_object* v_bs_1531_){
_start:
{
uint8_t v___x_1532_; 
v___x_1532_ = lean_usize_dec_lt(v_i_1530_, v_sz_1529_);
if (v___x_1532_ == 0)
{
return v_bs_1531_;
}
else
{
lean_object* v_v_1533_; lean_object* v___x_1534_; lean_object* v_bs_x27_1535_; lean_object* v___x_1536_; size_t v___x_1537_; size_t v___x_1538_; lean_object* v___x_1539_; 
v_v_1533_ = lean_array_uget(v_bs_1531_, v_i_1530_);
v___x_1534_ = lean_unsigned_to_nat(0u);
v_bs_x27_1535_ = lean_array_uset(v_bs_1531_, v_i_1530_, v___x_1534_);
v___x_1536_ = l_Lake_PackageEntry_toJson(v_v_1533_);
v___x_1537_ = ((size_t)1ULL);
v___x_1538_ = lean_usize_add(v_i_1530_, v___x_1537_);
v___x_1539_ = lean_array_uset(v_bs_x27_1535_, v_i_1530_, v___x_1536_);
v_i_1530_ = v___x_1538_;
v_bs_1531_ = v___x_1539_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1541_, lean_object* v_i_1542_, lean_object* v_bs_1543_){
_start:
{
size_t v_sz_boxed_1544_; size_t v_i_boxed_1545_; lean_object* v_res_1546_; 
v_sz_boxed_1544_ = lean_unbox_usize(v_sz_1541_);
lean_dec(v_sz_1541_);
v_i_boxed_1545_ = lean_unbox_usize(v_i_1542_);
lean_dec(v_i_1542_);
v_res_1546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(v_sz_boxed_1544_, v_i_boxed_1545_, v_bs_1543_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_Manifest_toJson_spec__0(lean_object* v_a_1547_){
_start:
{
size_t v_sz_1548_; size_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v_sz_1548_ = lean_array_size(v_a_1547_);
v___x_1549_ = ((size_t)0ULL);
v___x_1550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(v_sz_1548_, v___x_1549_, v_a_1547_);
v___x_1551_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
return v___x_1551_;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__1(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = ((lean_object*)(l_Lake_Manifest_version___closed__2));
v___x_1554_ = l_Lake_StdVer_toString(v___x_1553_);
return v___x_1554_;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__2(void){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__1, &l_Lake_Manifest_toJson___closed__1_once, _init_l_Lake_Manifest_toJson___closed__1);
v___x_1556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
return v___x_1556_;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__3(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__2, &l_Lake_Manifest_toJson___closed__2_once, _init_l_Lake_Manifest_toJson___closed__2);
v___x_1558_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__0));
v___x_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
lean_ctor_set(v___x_1559_, 1, v___x_1557_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_toJson(lean_object* v_self_1564_){
_start:
{
lean_object* v_name_1565_; lean_object* v_lakeDir_1566_; uint8_t v_fixedToolchain_1567_; lean_object* v_packagesDir_x3f_1568_; lean_object* v_packages_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v_name_1565_ = lean_ctor_get(v_self_1564_, 0);
lean_inc(v_name_1565_);
v_lakeDir_1566_ = lean_ctor_get(v_self_1564_, 1);
lean_inc_ref(v_lakeDir_1566_);
v_fixedToolchain_1567_ = lean_ctor_get_uint8(v_self_1564_, sizeof(void*)*4);
v_packagesDir_x3f_1568_ = lean_ctor_get(v_self_1564_, 2);
lean_inc(v_packagesDir_x3f_1568_);
v_packages_1569_ = lean_ctor_get(v_self_1564_, 3);
lean_inc_ref(v_packages_1569_);
lean_dec_ref(v_self_1564_);
v___x_1570_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__3, &l_Lake_Manifest_toJson___closed__3_once, _init_l_Lake_Manifest_toJson___closed__3);
v___x_1571_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__4));
v___x_1572_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1572_, 0, v_fixedToolchain_1567_);
v___x_1573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1571_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_1575_ = 1;
v___x_1576_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1565_, v___x_1575_);
v___x_1577_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
v___x_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1574_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__5));
v___x_1580_ = l_Lake_mkRelPathString(v_lakeDir_1566_);
v___x_1581_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
v___x_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1579_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__6));
v___x_1584_ = l_Lean_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_packagesDir_x3f_1568_);
v___x_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1583_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__7));
v___x_1587_ = l_Lean_Array_toJson___at___00Lake_Manifest_toJson_spec__0(v_packages_1569_);
v___x_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1586_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = lean_box(0);
v___x_1590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1585_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1582_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1578_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1573_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1570_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = l_Lean_Json_mkObj(v___x_1595_);
lean_dec_ref_known(v___x_1595_, 2);
return v___x_1596_;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6(void){
_start:
{
lean_object* v_natZero_1607_; lean_object* v_intZero_1608_; 
v_natZero_1607_ = lean_unsigned_to_nat(0u);
v_intZero_1608_ = lean_nat_to_int(v_natZero_1607_);
return v_intZero_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(lean_object* v_obj_1613_){
_start:
{
lean_object* v_ver_1615_; lean_object* v___y_1624_; lean_object* v_ver_1632_; lean_object* v_major_1633_; lean_object* v_a_1650_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__0));
v___x_1674_ = l_Lake_JsonObject_getJson_x3f(v_obj_1613_, v___x_1673_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7));
v___x_1676_ = l_Lake_JsonObject_getJson_x3f(v_obj_1613_, v___x_1675_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v___x_1677_; 
v___x_1677_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__9));
return v___x_1677_;
}
else
{
lean_object* v_val_1678_; 
v_val_1678_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_val_1678_);
lean_dec_ref_known(v___x_1676_, 1);
v_a_1650_ = v_val_1678_;
goto v___jp_1649_;
}
}
else
{
lean_object* v_val_1679_; 
v_val_1679_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_val_1679_);
lean_dec_ref_known(v___x_1674_, 1);
v_a_1650_ = v_val_1679_;
goto v___jp_1649_;
}
v___jp_1614_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1616_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__0));
v___x_1617_ = lean_unsigned_to_nat(80u);
v___x_1618_ = l_Lean_Json_pretty(v_ver_1615_, v___x_1617_);
v___x_1619_ = lean_string_append(v___x_1616_, v___x_1618_);
lean_dec_ref(v___x_1618_);
v___x_1620_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__1));
v___x_1621_ = lean_string_append(v___x_1619_, v___x_1620_);
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
v___jp_1623_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1625_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__2));
v___x_1626_ = l_Lake_SemVerCore_toString(v___y_1624_);
v___x_1627_ = lean_string_append(v___x_1625_, v___x_1626_);
lean_dec_ref(v___x_1626_);
v___x_1628_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1629_ = lean_string_append(v___x_1627_, v___x_1628_);
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
return v___x_1630_;
}
v___jp_1631_:
{
lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1634_ = lean_unsigned_to_nat(1u);
v___x_1635_ = lean_nat_dec_lt(v___x_1634_, v_major_1633_);
lean_dec(v_major_1633_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; uint8_t v___x_1637_; 
v___x_1636_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__3));
v___x_1637_ = l_Lake_instOrdSemVerCore_ord(v_ver_1632_, v___x_1636_);
if (v___x_1637_ == 0)
{
v___y_1624_ = v_ver_1632_;
goto v___jp_1623_;
}
else
{
if (v___x_1635_ == 0)
{
lean_object* v___x_1638_; 
v___x_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1638_, 0, v_ver_1632_);
return v___x_1638_;
}
else
{
v___y_1624_ = v_ver_1632_;
goto v___jp_1623_;
}
}
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1639_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4));
v___x_1640_ = l_Lake_SemVerCore_toString(v_ver_1632_);
v___x_1641_ = lean_string_append(v___x_1639_, v___x_1640_);
lean_dec_ref(v___x_1640_);
v___x_1642_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__5));
v___x_1643_ = lean_string_append(v___x_1641_, v___x_1642_);
v___x_1644_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__1, &l_Lake_Manifest_toJson___closed__1_once, _init_l_Lake_Manifest_toJson___closed__1);
v___x_1645_ = lean_string_append(v___x_1643_, v___x_1644_);
v___x_1646_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__1));
v___x_1647_ = lean_string_append(v___x_1645_, v___x_1646_);
v___x_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
return v___x_1648_;
}
}
v___jp_1649_:
{
switch(lean_obj_tag(v_a_1650_))
{
case 2:
{
lean_object* v_n_1651_; lean_object* v_mantissa_1652_; lean_object* v_exponent_1653_; lean_object* v_natZero_1654_; lean_object* v_intZero_1655_; uint8_t v_isNeg_1656_; 
v_n_1651_ = lean_ctor_get(v_a_1650_, 0);
v_mantissa_1652_ = lean_ctor_get(v_n_1651_, 0);
v_exponent_1653_ = lean_ctor_get(v_n_1651_, 1);
v_natZero_1654_ = lean_unsigned_to_nat(0u);
v_intZero_1655_ = lean_obj_once(&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6, &l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6_once, _init_l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6);
v_isNeg_1656_ = lean_int_dec_lt(v_mantissa_1652_, v_intZero_1655_);
if (v_isNeg_1656_ == 0)
{
uint8_t v___x_1657_; 
v___x_1657_ = lean_nat_dec_eq(v_exponent_1653_, v_natZero_1654_);
if (v___x_1657_ == 0)
{
v_ver_1615_ = v_a_1650_;
goto v___jp_1614_;
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1659_; 
lean_inc(v_mantissa_1652_);
lean_dec_ref_known(v_a_1650_, 1);
v_a_1658_ = lean_nat_abs(v_mantissa_1652_);
lean_dec(v_mantissa_1652_);
v___x_1659_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1659_, 0, v_natZero_1654_);
lean_ctor_set(v___x_1659_, 1, v_a_1658_);
lean_ctor_set(v___x_1659_, 2, v_natZero_1654_);
v_ver_1632_ = v___x_1659_;
v_major_1633_ = v_natZero_1654_;
goto v___jp_1631_;
}
}
else
{
v_ver_1615_ = v_a_1650_;
goto v___jp_1614_;
}
}
case 3:
{
lean_object* v_s_1660_; lean_object* v___x_1661_; 
v_s_1660_ = lean_ctor_get(v_a_1650_, 0);
lean_inc_ref(v_s_1660_);
lean_dec_ref_known(v_a_1650_, 1);
v___x_1661_ = l_Lake_StdVer_parse(v_s_1660_);
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
lean_object* v_a_1670_; lean_object* v_toSemVerCore_1671_; lean_object* v_major_1672_; 
v_a_1670_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1670_);
lean_dec_ref_known(v___x_1661_, 1);
v_toSemVerCore_1671_ = lean_ctor_get(v_a_1670_, 0);
lean_inc_ref(v_toSemVerCore_1671_);
lean_dec(v_a_1670_);
v_major_1672_ = lean_ctor_get(v_toSemVerCore_1671_, 0);
lean_inc(v_major_1672_);
v_ver_1632_ = v_toSemVerCore_1671_;
v_major_1633_ = v_major_1672_;
goto v___jp_1631_;
}
}
default: 
{
v_ver_1615_ = v_a_1650_;
goto v___jp_1614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___boxed(lean_object* v_obj_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_obj_1680_);
lean_dec(v_obj_1680_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(size_t v_sz_1682_, size_t v_i_1683_, lean_object* v_bs_1684_){
_start:
{
uint8_t v___x_1685_; 
v___x_1685_ = lean_usize_dec_lt(v_i_1683_, v_sz_1682_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; 
v___x_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1686_, 0, v_bs_1684_);
return v___x_1686_;
}
else
{
lean_object* v_v_1687_; lean_object* v___x_1688_; 
v_v_1687_ = lean_array_uget_borrowed(v_bs_1684_, v_i_1683_);
lean_inc(v_v_1687_);
v___x_1688_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson(v_v_1687_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_dec_ref(v_bs_1684_);
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1688_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1688_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1698_; lean_object* v_bs_x27_1699_; size_t v___x_1700_; size_t v___x_1701_; lean_object* v___x_1702_; 
v_a_1697_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1697_);
lean_dec_ref_known(v___x_1688_, 1);
v___x_1698_ = lean_unsigned_to_nat(0u);
v_bs_x27_1699_ = lean_array_uset(v_bs_1684_, v_i_1683_, v___x_1698_);
v___x_1700_ = ((size_t)1ULL);
v___x_1701_ = lean_usize_add(v_i_1683_, v___x_1700_);
v___x_1702_ = lean_array_uset(v_bs_x27_1699_, v_i_1683_, v_a_1697_);
v_i_1683_ = v___x_1701_;
v_bs_1684_ = v___x_1702_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_1704_, lean_object* v_i_1705_, lean_object* v_bs_1706_){
_start:
{
size_t v_sz_boxed_1707_; size_t v_i_boxed_1708_; lean_object* v_res_1709_; 
v_sz_boxed_1707_ = lean_unbox_usize(v_sz_1704_);
lean_dec(v_sz_1704_);
v_i_boxed_1708_ = lean_unbox_usize(v_i_1705_);
lean_dec(v_i_1705_);
v_res_1709_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(v_sz_boxed_1707_, v_i_boxed_1708_, v_bs_1706_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3(lean_object* v_x_1711_){
_start:
{
if (lean_obj_tag(v_x_1711_) == 4)
{
lean_object* v_elems_1712_; size_t v_sz_1713_; size_t v___x_1714_; lean_object* v___x_1715_; 
v_elems_1712_ = lean_ctor_get(v_x_1711_, 0);
lean_inc_ref(v_elems_1712_);
lean_dec_ref_known(v_x_1711_, 1);
v_sz_1713_ = lean_array_size(v_elems_1712_);
v___x_1714_ = ((size_t)0ULL);
v___x_1715_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(v_sz_1713_, v___x_1714_, v_elems_1712_);
return v___x_1715_;
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1716_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3___closed__0));
v___x_1717_ = lean_unsigned_to_nat(80u);
v___x_1718_ = l_Lean_Json_pretty(v_x_1711_, v___x_1717_);
v___x_1719_ = lean_string_append(v___x_1716_, v___x_1718_);
lean_dec_ref(v___x_1718_);
v___x_1720_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1721_ = lean_string_append(v___x_1719_, v___x_1720_);
v___x_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
return v___x_1722_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2(lean_object* v_x_1725_){
_start:
{
if (lean_obj_tag(v_x_1725_) == 0)
{
lean_object* v___x_1726_; 
v___x_1726_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2___closed__0));
return v___x_1726_;
}
else
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3(v_x_1725_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1727_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1727_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1744_; 
v_a_1736_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1738_ = v___x_1727_;
v_isShared_1739_ = v_isSharedCheck_1744_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1727_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1744_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1740_; lean_object* v___x_1742_; 
v___x_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1740_, 0, v_a_1736_);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v___x_1740_);
v___x_1742_ = v___x_1738_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(size_t v_sz_1745_, size_t v_i_1746_, lean_object* v_bs_1747_){
_start:
{
uint8_t v___x_1748_; 
v___x_1748_ = lean_usize_dec_lt(v_i_1746_, v_sz_1745_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; 
v___x_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1749_, 0, v_bs_1747_);
return v___x_1749_;
}
else
{
lean_object* v_v_1750_; lean_object* v___x_1751_; 
v_v_1750_ = lean_array_uget_borrowed(v_bs_1747_, v_i_1746_);
lean_inc(v_v_1750_);
v___x_1751_ = l_Lake_PackageEntry_fromJson_x3f(v_v_1750_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_dec_ref(v_bs_1747_);
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1751_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1751_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1761_; lean_object* v_bs_x27_1762_; size_t v___x_1763_; size_t v___x_1764_; lean_object* v___x_1765_; 
v_a_1760_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1760_);
lean_dec_ref_known(v___x_1751_, 1);
v___x_1761_ = lean_unsigned_to_nat(0u);
v_bs_x27_1762_ = lean_array_uset(v_bs_1747_, v_i_1746_, v___x_1761_);
v___x_1763_ = ((size_t)1ULL);
v___x_1764_ = lean_usize_add(v_i_1746_, v___x_1763_);
v___x_1765_ = lean_array_uset(v_bs_x27_1762_, v_i_1746_, v_a_1760_);
v_i_1746_ = v___x_1764_;
v_bs_1747_ = v___x_1765_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_1767_, lean_object* v_i_1768_, lean_object* v_bs_1769_){
_start:
{
size_t v_sz_boxed_1770_; size_t v_i_boxed_1771_; lean_object* v_res_1772_; 
v_sz_boxed_1770_ = lean_unbox_usize(v_sz_1767_);
lean_dec(v_sz_1767_);
v_i_boxed_1771_ = lean_unbox_usize(v_i_1768_);
lean_dec(v_i_1768_);
v_res_1772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(v_sz_boxed_1770_, v_i_boxed_1771_, v_bs_1769_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1(lean_object* v_x_1773_){
_start:
{
if (lean_obj_tag(v_x_1773_) == 4)
{
lean_object* v_elems_1774_; size_t v_sz_1775_; size_t v___x_1776_; lean_object* v___x_1777_; 
v_elems_1774_ = lean_ctor_get(v_x_1773_, 0);
lean_inc_ref(v_elems_1774_);
lean_dec_ref_known(v_x_1773_, 1);
v_sz_1775_ = lean_array_size(v_elems_1774_);
v___x_1776_ = ((size_t)0ULL);
v___x_1777_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(v_sz_1775_, v___x_1776_, v_elems_1774_);
return v___x_1777_;
}
else
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1778_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3___closed__0));
v___x_1779_ = lean_unsigned_to_nat(80u);
v___x_1780_ = l_Lean_Json_pretty(v_x_1773_, v___x_1779_);
v___x_1781_ = lean_string_append(v___x_1778_, v___x_1780_);
lean_dec_ref(v___x_1780_);
v___x_1782_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1783_ = lean_string_append(v___x_1781_, v___x_1782_);
v___x_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
return v___x_1784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1(lean_object* v_x_1787_){
_start:
{
if (lean_obj_tag(v_x_1787_) == 0)
{
lean_object* v___x_1788_; 
v___x_1788_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1___closed__0));
return v___x_1788_;
}
else
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1(v_x_1787_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1789_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1806_; 
v_a_1798_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1800_ = v___x_1789_;
v_isShared_1801_ = v_isSharedCheck_1806_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1789_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1806_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v___x_1804_; 
v___x_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1802_, 0, v_a_1798_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1802_);
v___x_1804_ = v___x_1800_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(size_t v_sz_1807_, size_t v_i_1808_, lean_object* v_bs_1809_){
_start:
{
uint8_t v___x_1810_; 
v___x_1810_ = lean_usize_dec_lt(v_i_1808_, v_sz_1807_);
if (v___x_1810_ == 0)
{
return v_bs_1809_;
}
else
{
lean_object* v_v_1811_; lean_object* v___x_1812_; lean_object* v_bs_x27_1813_; lean_object* v___x_1814_; size_t v___x_1815_; size_t v___x_1816_; lean_object* v___x_1817_; 
v_v_1811_ = lean_array_uget(v_bs_1809_, v_i_1808_);
v___x_1812_ = lean_unsigned_to_nat(0u);
v_bs_x27_1813_ = lean_array_uset(v_bs_1809_, v_i_1808_, v___x_1812_);
v___x_1814_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(v_v_1811_);
lean_dec(v_v_1811_);
v___x_1815_ = ((size_t)1ULL);
v___x_1816_ = lean_usize_add(v_i_1808_, v___x_1815_);
v___x_1817_ = lean_array_uset(v_bs_x27_1813_, v_i_1808_, v___x_1814_);
v_i_1808_ = v___x_1816_;
v_bs_1809_ = v___x_1817_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0___boxed(lean_object* v_sz_1819_, lean_object* v_i_1820_, lean_object* v_bs_1821_){
_start:
{
size_t v_sz_boxed_1822_; size_t v_i_boxed_1823_; lean_object* v_res_1824_; 
v_sz_boxed_1822_ = lean_unbox_usize(v_sz_1819_);
lean_dec(v_sz_1819_);
v_i_boxed_1823_ = lean_unbox_usize(v_i_1820_);
lean_dec(v_i_1820_);
v_res_1824_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(v_sz_boxed_1822_, v_i_boxed_1823_, v_bs_1821_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(lean_object* v_ver_1838_, lean_object* v_obj_1839_){
_start:
{
lean_object* v_a_1841_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1850_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__4));
v___x_1851_ = l_Lake_StdVer_compare(v_ver_1838_, v___x_1850_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__7));
v___x_1853_ = l_Lake_JsonObject_getJson_x3f(v_obj_1839_, v___x_1852_);
if (lean_obj_tag(v___x_1853_) == 0)
{
goto v___jp_1846_;
}
else
{
lean_object* v_val_1854_; lean_object* v___x_1855_; 
v_val_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_val_1854_);
lean_dec_ref_known(v___x_1853_, 1);
v___x_1855_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2(v_val_1854_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1865_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1858_ = v___x_1855_;
v_isShared_1859_ = v_isSharedCheck_1865_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1855_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1865_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1863_; 
v___x_1860_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5));
v___x_1861_ = lean_string_append(v___x_1860_, v_a_1856_);
lean_dec(v_a_1856_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1861_);
v___x_1863_ = v___x_1858_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
v_a_1866_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1855_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1855_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
lean_ctor_set_tag(v___x_1868_, 0);
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
else
{
lean_object* v_a_1874_; 
v_a_1874_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1874_);
lean_dec_ref_known(v___x_1855_, 1);
if (lean_obj_tag(v_a_1874_) == 0)
{
goto v___jp_1846_;
}
else
{
lean_object* v_val_1875_; 
v_val_1875_ = lean_ctor_get(v_a_1874_, 0);
lean_inc(v_val_1875_);
lean_dec_ref_known(v_a_1874_, 1);
v_a_1841_ = v_val_1875_;
goto v___jp_1840_;
}
}
}
}
}
else
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__7));
v___x_1877_ = l_Lake_JsonObject_getJson_x3f(v_obj_1839_, v___x_1876_);
if (lean_obj_tag(v___x_1877_) == 0)
{
goto v___jp_1848_;
}
else
{
lean_object* v_val_1878_; lean_object* v___x_1879_; 
v_val_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_val_1878_);
lean_dec_ref_known(v___x_1877_, 1);
v___x_1879_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1(v_val_1878_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1889_; 
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1882_ = v___x_1879_;
v_isShared_1883_ = v_isSharedCheck_1889_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1879_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1889_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1884_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5));
v___x_1885_ = lean_string_append(v___x_1884_, v_a_1880_);
lean_dec(v_a_1880_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v___x_1885_);
v___x_1887_ = v___x_1882_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1885_);
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
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
v_a_1890_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1879_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1879_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
lean_ctor_set_tag(v___x_1892_, 0);
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
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1906_; 
v_a_1898_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1900_ = v___x_1879_;
v_isShared_1901_ = v_isSharedCheck_1906_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1879_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1906_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
if (lean_obj_tag(v_a_1898_) == 0)
{
lean_del_object(v___x_1900_);
goto v___jp_1848_;
}
else
{
lean_object* v_val_1902_; lean_object* v___x_1904_; 
v_val_1902_ = lean_ctor_get(v_a_1898_, 0);
lean_inc(v_val_1902_);
lean_dec_ref_known(v_a_1898_, 1);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 0, v_val_1902_);
v___x_1904_ = v___x_1900_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_val_1902_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
}
}
}
v___jp_1840_:
{
size_t v_sz_1842_; size_t v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v_sz_1842_ = lean_array_size(v_a_1841_);
v___x_1843_ = ((size_t)0ULL);
v___x_1844_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(v_sz_1842_, v___x_1843_, v_a_1841_);
v___x_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
return v___x_1845_;
}
v___jp_1846_:
{
lean_object* v___x_1847_; 
v___x_1847_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__0));
v_a_1841_ = v___x_1847_;
goto v___jp_1840_;
}
v___jp_1848_:
{
lean_object* v___x_1849_; 
v___x_1849_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__2));
return v___x_1849_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___boxed(lean_object* v_ver_1907_, lean_object* v_obj_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(v_ver_1907_, v_obj_1908_);
lean_dec(v_obj_1908_);
lean_dec_ref(v_ver_1907_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0(lean_object* v_x_1912_){
_start:
{
if (lean_obj_tag(v_x_1912_) == 0)
{
lean_object* v___x_1913_; 
v___x_1913_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0___closed__0));
return v___x_1913_;
}
else
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_Name_fromJson_x3f(v_x_1912_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1914_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1914_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1931_; 
v_a_1923_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1925_ = v___x_1914_;
v_isShared_1926_ = v_isSharedCheck_1931_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1914_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1931_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1927_; lean_object* v___x_1929_; 
v___x_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1927_, 0, v_a_1923_);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 0, v___x_1927_);
v___x_1929_ = v___x_1925_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_fromJson_x3f(lean_object* v_json_1935_){
_start:
{
lean_object* v___x_1936_; 
v___x_1936_ = l_Lean_Json_getObj_x3f(v_json_1935_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1946_; 
v_a_1945_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1936_, 1);
v___x_1946_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_a_1945_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec(v_a_1945_);
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1946_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
else
{
lean_object* v_a_1955_; lean_object* v___y_1957_; uint8_t v___y_1958_; lean_object* v___y_1959_; lean_object* v_a_1960_; uint8_t v___y_1982_; lean_object* v___y_1983_; lean_object* v_a_1984_; uint8_t v___y_2010_; lean_object* v___y_2011_; uint8_t v___y_2014_; lean_object* v_a_2015_; uint8_t v___y_2041_; uint8_t v_a_2044_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v_a_1955_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1955_);
lean_dec_ref_known(v___x_1946_, 1);
v___x_2071_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__4));
v___x_2072_ = l_Lake_JsonObject_getJson_x3f(v_a_1945_, v___x_2071_);
if (lean_obj_tag(v___x_2072_) == 0)
{
goto v___jp_2069_;
}
else
{
lean_object* v_val_2073_; lean_object* v___x_2074_; 
v_val_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_val_2073_);
lean_dec_ref_known(v___x_2072_, 1);
v___x_2074_ = l_Lean_Option_fromJson_x3f___at___00Lake_PackageEntry_fromJson_x3f_spec__0(v_val_2073_);
lean_dec(v_val_2073_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2084_; 
lean_dec(v_a_1955_);
lean_dec(v_a_1945_);
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2077_ = v___x_2074_;
v_isShared_2078_ = v_isSharedCheck_2084_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2074_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2084_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2079_ = ((lean_object*)(l_Lake_Manifest_fromJson_x3f___closed__2));
v___x_2080_ = lean_string_append(v___x_2079_, v_a_2075_);
lean_dec(v_a_2075_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2080_);
v___x_2082_ = v___x_2077_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
else
{
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec(v_a_1955_);
lean_dec(v_a_1945_);
v_a_2085_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2074_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2074_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
lean_ctor_set_tag(v___x_2087_, 0);
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
else
{
lean_object* v_a_2093_; 
v_a_2093_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2074_, 1);
if (lean_obj_tag(v_a_2093_) == 0)
{
goto v___jp_2069_;
}
else
{
lean_object* v_val_2094_; uint8_t v___x_2095_; 
v_val_2094_ = lean_ctor_get(v_a_2093_, 0);
lean_inc(v_val_2094_);
lean_dec_ref_known(v_a_2093_, 1);
v___x_2095_ = lean_unbox(v_val_2094_);
lean_dec(v_val_2094_);
v_a_2044_ = v___x_2095_;
goto v___jp_2043_;
}
}
}
}
v___jp_1956_:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1961_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1962_, 0, v_a_1955_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(v___x_1962_, v_a_1945_);
lean_dec(v_a_1945_);
lean_dec_ref_known(v___x_1962_, 2);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec(v_a_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1957_);
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1963_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1963_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1980_; 
v_a_1972_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1974_ = v___x_1963_;
v_isShared_1975_ = v_isSharedCheck_1980_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1963_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1980_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1976_; lean_object* v___x_1978_; 
v___x_1976_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1976_, 0, v___y_1959_);
lean_ctor_set(v___x_1976_, 1, v___y_1957_);
lean_ctor_set(v___x_1976_, 2, v_a_1960_);
lean_ctor_set(v___x_1976_, 3, v_a_1972_);
lean_ctor_set_uint8(v___x_1976_, sizeof(void*)*4, v___y_1958_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 0, v___x_1976_);
v___x_1978_ = v___x_1974_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
v___jp_1981_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__6));
v___x_1986_ = l_Lake_JsonObject_getJson_x3f(v_a_1945_, v___x_1985_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v___x_1987_; 
v___x_1987_ = lean_box(0);
v___y_1957_ = v_a_1984_;
v___y_1958_ = v___y_1982_;
v___y_1959_ = v___y_1983_;
v_a_1960_ = v___x_1987_;
goto v___jp_1956_;
}
else
{
lean_object* v_val_1988_; lean_object* v___x_1989_; 
v_val_1988_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_val_1988_);
lean_dec_ref_known(v___x_1986_, 1);
v___x_1989_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1988_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1999_; 
lean_dec_ref(v_a_1984_);
lean_dec(v___y_1983_);
lean_dec(v_a_1955_);
lean_dec(v_a_1945_);
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
v___x_1994_ = ((lean_object*)(l_Lake_Manifest_fromJson_x3f___closed__0));
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
lean_dec_ref(v_a_1984_);
lean_dec(v___y_1983_);
lean_dec(v_a_1955_);
lean_dec(v_a_1945_);
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
lean_dec_ref_known(v___x_1989_, 1);
v___y_1957_ = v_a_1984_;
v___y_1958_ = v___y_1982_;
v___y_1959_ = v___y_1983_;
v_a_1960_ = v_a_2008_;
goto v___jp_1956_;
}
}
}
}
v___jp_2009_:
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Lake_defaultLakeDir;
v___y_1982_ = v___y_2010_;
v___y_1983_ = v___y_2011_;
v_a_1984_ = v___x_2012_;
goto v___jp_1981_;
}
v___jp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__5));
v___x_2017_ = l_Lake_JsonObject_getJson_x3f(v_a_1945_, v___x_2016_);
if (lean_obj_tag(v___x_2017_) == 0)
{
v___y_2010_ = v___y_2014_;
v___y_2011_ = v_a_2015_;
goto v___jp_2009_;
}
else
{
lean_object* v_val_2018_; lean_object* v___x_2019_; 
v_val_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_val_2018_);
lean_dec_ref_known(v___x_2017_, 1);
v___x_2019_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_2018_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2029_; 
lean_dec(v_a_2015_);
lean_dec(v_a_1955_);
lean_dec(v_a_1945_);
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2022_ = v___x_2019_;
v_isShared_2023_ = v_isSharedCheck_2029_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2019_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2029_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2024_ = ((lean_object*)(l_Lake_Manifest_fromJson_x3f___closed__1));
v___x_2025_ = lean_string_append(v___x_2024_, v_a_2020_);
lean_dec(v_a_2020_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v___x_2025_);
v___x_2027_ = v___x_2022_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec(v_a_2015_);
lean_dec(v_a_1955_);
lean_dec(v_a_1945_);
v_a_2030_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2019_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2019_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
lean_ctor_set_tag(v___x_2032_, 0);
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
else
{
lean_object* v_a_2038_; 
v_a_2038_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2038_);
lean_dec_ref_known(v___x_2019_, 1);
if (lean_obj_tag(v_a_2038_) == 0)
{
v___y_2010_ = v___y_2014_;
v___y_2011_ = v_a_2015_;
goto v___jp_2009_;
}
else
{
lean_object* v_val_2039_; 
v_val_2039_ = lean_ctor_get(v_a_2038_, 0);
lean_inc(v_val_2039_);
lean_dec_ref_known(v_a_2038_, 1);
v___y_1982_ = v___y_2014_;
v___y_1983_ = v_a_2015_;
v_a_1984_ = v_val_2039_;
goto v___jp_1981_;
}
}
}
}
}
v___jp_2040_:
{
lean_object* v___x_2042_; 
v___x_2042_ = lean_box(0);
v___y_2014_ = v___y_2041_;
v_a_2015_ = v___x_2042_;
goto v___jp_2013_;
}
v___jp_2043_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_2046_ = l_Lake_JsonObject_getJson_x3f(v_a_1945_, v___x_2045_);
if (lean_obj_tag(v___x_2046_) == 0)
{
v___y_2041_ = v_a_2044_;
goto v___jp_2040_;
}
else
{
lean_object* v_val_2047_; lean_object* v___x_2048_; 
v_val_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_val_2047_);
lean_dec_ref_known(v___x_2046_, 1);
v___x_2048_ = l_Lean_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0(v_val_2047_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v_a_1955_);
lean_dec(v_a_1945_);
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2051_ = v___x_2048_;
v_isShared_2052_ = v_isSharedCheck_2058_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2048_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2058_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2056_; 
v___x_2053_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__1));
v___x_2054_ = lean_string_append(v___x_2053_, v_a_2049_);
lean_dec(v_a_2049_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v___x_2054_);
v___x_2056_ = v___x_2051_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
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
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec(v_a_1955_);
lean_dec(v_a_1945_);
v_a_2059_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2048_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2048_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set_tag(v___x_2061_, 0);
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
else
{
lean_object* v_a_2067_; 
v_a_2067_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2067_);
lean_dec_ref_known(v___x_2048_, 1);
if (lean_obj_tag(v_a_2067_) == 0)
{
v___y_2041_ = v_a_2044_;
goto v___jp_2040_;
}
else
{
lean_object* v_val_2068_; 
v_val_2068_ = lean_ctor_get(v_a_2067_, 0);
lean_inc(v_val_2068_);
lean_dec_ref_known(v_a_2067_, 1);
v___y_2014_ = v_a_2044_;
v_a_2015_ = v_val_2068_;
goto v___jp_2013_;
}
}
}
}
}
v___jp_2069_:
{
uint8_t v___x_2070_; 
v___x_2070_ = 0;
v_a_2044_ = v___x_2070_;
goto v___jp_2043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_parse(lean_object* v_data_2099_){
_start:
{
lean_object* v___x_2100_; 
v___x_2100_ = l_Lean_Json_parse(v_data_2099_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2110_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2103_ = v___x_2100_;
v_isShared_2104_ = v_isSharedCheck_2110_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2100_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2110_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2105_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2106_ = lean_string_append(v___x_2105_, v_a_2101_);
lean_dec(v_a_2101_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 0, v___x_2106_);
v___x_2108_ = v___x_2103_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2112_; 
v_a_2111_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2111_);
lean_dec_ref_known(v___x_2100_, 1);
v___x_2112_ = l_Lake_Manifest_fromJson_x3f(v_a_2111_);
return v___x_2112_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load(lean_object* v_file_2114_){
_start:
{
lean_object* v___x_2116_; 
v___x_2116_ = l_IO_FS_readFile(v_file_2114_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2145_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2119_ = v___x_2116_;
v_isShared_2120_ = v_isSharedCheck_2145_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2116_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2145_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v_a_2122_; lean_object* v___x_2130_; 
v___x_2130_ = l_Lean_Json_parse(v_a_2117_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2132_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2133_ = lean_string_append(v___x_2132_, v_a_2131_);
lean_dec(v_a_2131_);
v_a_2122_ = v___x_2133_;
goto v___jp_2121_;
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2135_; 
v_a_2134_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2135_ = l_Lake_Manifest_fromJson_x3f(v_a_2134_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
v_a_2122_ = v_a_2136_;
goto v___jp_2121_;
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_del_object(v___x_2119_);
lean_dec_ref(v_file_2114_);
v_a_2137_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2135_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2135_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
lean_ctor_set_tag(v___x_2139_, 0);
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
v___jp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2128_; 
v___x_2123_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2124_ = lean_string_append(v_file_2114_, v___x_2123_);
v___x_2125_ = lean_string_append(v___x_2124_, v_a_2122_);
lean_dec_ref(v_a_2122_);
v___x_2126_ = lean_mk_io_user_error(v___x_2125_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set_tag(v___x_2119_, 1);
lean_ctor_set(v___x_2119_, 0, v___x_2126_);
v___x_2128_ = v___x_2119_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec_ref(v_file_2114_);
v_a_2146_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2116_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2116_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load___boxed(lean_object* v_file_2154_, lean_object* v_a_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lake_Manifest_load(v_file_2154_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f(lean_object* v_file_2157_){
_start:
{
lean_object* v_a_2160_; lean_object* v___x_2164_; 
v___x_2164_ = l_IO_FS_readFile(v_file_2157_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2193_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2167_ = v___x_2164_;
v_isShared_2168_ = v_isSharedCheck_2193_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2164_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2193_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v_a_2170_; lean_object* v___x_2175_; 
v___x_2175_ = l_Lean_Json_parse(v_a_2165_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
lean_del_object(v___x_2167_);
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2175_, 1);
v___x_2177_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2178_ = lean_string_append(v___x_2177_, v_a_2176_);
lean_dec(v_a_2176_);
v_a_2170_ = v___x_2178_;
goto v___jp_2169_;
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2180_; 
v_a_2179_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2179_);
lean_dec_ref_known(v___x_2175_, 1);
v___x_2180_ = l_Lake_Manifest_fromJson_x3f(v_a_2179_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; 
lean_del_object(v___x_2167_);
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___x_2180_, 1);
v_a_2170_ = v_a_2181_;
goto v___jp_2169_;
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2192_; 
lean_dec_ref(v_file_2157_);
v_a_2182_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2184_ = v___x_2180_;
v_isShared_2185_ = v_isSharedCheck_2192_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2180_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2192_;
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
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2189_; 
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v___x_2187_);
v___x_2189_ = v___x_2167_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
v___jp_2169_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2171_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2172_ = lean_string_append(v_file_2157_, v___x_2171_);
v___x_2173_ = lean_string_append(v___x_2172_, v_a_2170_);
lean_dec_ref(v_a_2170_);
v___x_2174_ = lean_mk_io_user_error(v___x_2173_);
v_a_2160_ = v___x_2174_;
goto v___jp_2159_;
}
}
}
else
{
lean_object* v_a_2194_; 
lean_dec_ref(v_file_2157_);
v_a_2194_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2194_);
lean_dec_ref_known(v___x_2164_, 1);
v_a_2160_ = v_a_2194_;
goto v___jp_2159_;
}
v___jp_2159_:
{
if (lean_obj_tag(v_a_2160_) == 11)
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
lean_dec_ref_known(v_a_2160_, 2);
v___x_2161_ = lean_box(0);
v___x_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
return v___x_2162_;
}
else
{
lean_object* v___x_2163_; 
v___x_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2163_, 0, v_a_2160_);
return v___x_2163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f___boxed(lean_object* v_file_2195_, lean_object* v_a_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Lake_Manifest_load_x3f(v_file_2195_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_save(lean_object* v_self_2198_, lean_object* v_manifestFile_2199_){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v_contents_2203_; uint32_t v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2201_ = l_Lake_Manifest_toJson(v_self_2198_);
v___x_2202_ = lean_unsigned_to_nat(80u);
v_contents_2203_ = l_Lean_Json_pretty(v___x_2201_, v___x_2202_);
v___x_2204_ = 10;
v___x_2205_ = lean_string_push(v_contents_2203_, v___x_2204_);
v___x_2206_ = l_IO_FS_writeFile(v_manifestFile_2199_, v___x_2205_);
lean_dec_ref(v___x_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_save___boxed(lean_object* v_self_2207_, lean_object* v_manifestFile_2208_, lean_object* v_a_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Lake_Manifest_save(v_self_2207_, v_manifestFile_2208_);
lean_dec_ref(v_manifestFile_2208_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_decodeEntries(lean_object* v_data_2211_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l_Lean_Json_getObj_x3f(v_data_2211_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2212_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2212_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2222_; 
v_a_2221_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2221_);
lean_dec_ref_known(v___x_2212_, 1);
v___x_2222_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_a_2221_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec(v_a_2221_);
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2222_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2222_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v_a_2231_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_a_2231_);
lean_dec_ref_known(v___x_2222_, 1);
v___x_2232_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_2233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2233_, 0, v_a_2231_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
v___x_2234_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(v___x_2233_, v_a_2221_);
lean_dec(v_a_2221_);
lean_dec_ref_known(v___x_2233_, 2);
return v___x_2234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_parseEntries(lean_object* v_data_2235_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_Json_parse(v_data_2235_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2246_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2239_ = v___x_2236_;
v_isShared_2240_ = v_isSharedCheck_2246_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2236_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2246_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2244_; 
v___x_2241_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2242_ = lean_string_append(v___x_2241_, v_a_2237_);
lean_dec(v_a_2237_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v___x_2242_);
v___x_2244_ = v___x_2239_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2242_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2248_; 
v_a_2247_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___x_2236_, 1);
v___x_2248_ = l_Lake_Manifest_decodeEntries(v_a_2247_);
return v___x_2248_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_loadEntries(lean_object* v_file_2249_){
_start:
{
lean_object* v___x_2251_; 
v___x_2251_ = l_IO_FS_readFile(v_file_2249_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2280_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2254_ = v___x_2251_;
v_isShared_2255_ = v_isSharedCheck_2280_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2251_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2280_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v_a_2257_; lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_Json_parse(v_a_2252_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
lean_dec_ref_known(v___x_2265_, 1);
v___x_2267_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2268_ = lean_string_append(v___x_2267_, v_a_2266_);
lean_dec(v_a_2266_);
v_a_2257_ = v___x_2268_;
goto v___jp_2256_;
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2270_; 
v_a_2269_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2269_);
lean_dec_ref_known(v___x_2265_, 1);
v___x_2270_ = l_Lake_Manifest_decodeEntries(v_a_2269_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2271_);
lean_dec_ref_known(v___x_2270_, 1);
v_a_2257_ = v_a_2271_;
goto v___jp_2256_;
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_del_object(v___x_2254_);
lean_dec_ref(v_file_2249_);
v_a_2272_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2270_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2270_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
lean_ctor_set_tag(v___x_2274_, 0);
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
v___jp_2256_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2263_; 
v___x_2258_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2259_ = lean_string_append(v_file_2249_, v___x_2258_);
v___x_2260_ = lean_string_append(v___x_2259_, v_a_2257_);
lean_dec_ref(v_a_2257_);
v___x_2261_ = lean_mk_io_user_error(v___x_2260_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set_tag(v___x_2254_, 1);
lean_ctor_set(v___x_2254_, 0, v___x_2261_);
v___x_2263_ = v___x_2254_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
lean_dec_ref(v_file_2249_);
v_a_2281_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2251_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2251_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_loadEntries___boxed(lean_object* v_file_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lake_Manifest_loadEntries(v_file_2289_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries(lean_object* v_file_2292_){
_start:
{
lean_object* v_a_2295_; lean_object* v___x_2304_; 
v___x_2304_ = l_IO_FS_readFile(v_file_2292_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2326_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2307_ = v___x_2304_;
v_isShared_2308_ = v_isSharedCheck_2326_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2304_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2326_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v_a_2310_; lean_object* v___x_2315_; 
v___x_2315_ = l_Lean_Json_parse(v_a_2305_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
lean_del_object(v___x_2307_);
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v___x_2317_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2318_ = lean_string_append(v___x_2317_, v_a_2316_);
lean_dec(v_a_2316_);
v_a_2310_ = v___x_2318_;
goto v___jp_2309_;
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2320_; 
v_a_2319_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2315_, 1);
v___x_2320_ = l_Lake_Manifest_decodeEntries(v_a_2319_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; 
lean_del_object(v___x_2307_);
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2320_, 1);
v_a_2310_ = v_a_2321_;
goto v___jp_2309_;
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; 
lean_dec_ref(v_file_2292_);
v_a_2322_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2322_);
lean_dec_ref_known(v___x_2320_, 1);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v_a_2322_);
v___x_2324_ = v___x_2307_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2322_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
v___jp_2309_:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2311_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
lean_inc_ref(v_file_2292_);
v___x_2312_ = lean_string_append(v_file_2292_, v___x_2311_);
v___x_2313_ = lean_string_append(v___x_2312_, v_a_2310_);
lean_dec_ref(v_a_2310_);
v___x_2314_ = lean_mk_io_user_error(v___x_2313_);
v_a_2295_ = v___x_2314_;
goto v___jp_2294_;
}
}
}
else
{
lean_object* v_a_2327_; 
v_a_2327_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2327_);
lean_dec_ref_known(v___x_2304_, 1);
v_a_2295_ = v_a_2327_;
goto v___jp_2294_;
}
v___jp_2294_:
{
if (lean_obj_tag(v_a_2295_) == 11)
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
lean_dec_ref_known(v_a_2295_, 2);
lean_dec_ref(v_file_2292_);
v___x_2296_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__1));
v___x_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
return v___x_2297_;
}
else
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2298_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2299_ = lean_string_append(v_file_2292_, v___x_2298_);
v___x_2300_ = lean_io_error_to_string(v_a_2295_);
v___x_2301_ = lean_string_append(v___x_2299_, v___x_2300_);
lean_dec_ref(v___x_2300_);
v___x_2302_ = lean_mk_io_user_error(v___x_2301_);
v___x_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
return v___x_2303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries___boxed(lean_object* v_file_2328_, lean_object* v_a_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lake_Manifest_tryLoadEntries(v_file_2328_);
return v_res_2330_;
}
}
static lean_object* _init_l_Lake_Manifest_saveEntries___closed__0(void){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2331_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__2, &l_Lake_Manifest_toJson___closed__2_once, _init_l_Lake_Manifest_toJson___closed__2);
v___x_2332_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7));
v___x_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
lean_ctor_set(v___x_2333_, 1, v___x_2331_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries(lean_object* v_file_2334_, lean_object* v_entries_2335_){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v_contents_2346_; uint32_t v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2337_ = lean_obj_once(&l_Lake_Manifest_saveEntries___closed__0, &l_Lake_Manifest_saveEntries___closed__0_once, _init_l_Lake_Manifest_saveEntries___closed__0);
v___x_2338_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__7));
v___x_2339_ = l_Lean_Array_toJson___at___00Lake_Manifest_toJson_spec__0(v_entries_2335_);
v___x_2340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2338_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
v___x_2341_ = lean_box(0);
v___x_2342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2340_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
v___x_2343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2337_);
lean_ctor_set(v___x_2343_, 1, v___x_2342_);
v___x_2344_ = l_Lean_Json_mkObj(v___x_2343_);
lean_dec_ref_known(v___x_2343_, 2);
v___x_2345_ = lean_unsigned_to_nat(80u);
v_contents_2346_ = l_Lean_Json_pretty(v___x_2344_, v___x_2345_);
v___x_2347_ = 10;
v___x_2348_ = lean_string_push(v_contents_2346_, v___x_2347_);
v___x_2349_ = l_IO_FS_writeFile(v_file_2334_, v___x_2348_);
lean_dec_ref(v___x_2348_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries___boxed(lean_object* v_file_2350_, lean_object* v_entries_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lake_Manifest_saveEntries(v_file_2350_, v_entries_2351_);
lean_dec_ref(v_file_2350_);
return v_res_2353_;
}
}
lean_object* runtime_initialize_Lake_Util_Version(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Defaults(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Error(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_FilePath(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Coe(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Load_Manifest(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
