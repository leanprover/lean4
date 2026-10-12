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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorIdx___impl(lean_object* v_x_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_tag_nat(v_x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorIdx___impl___boxed(lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorIdx___impl(v_x_12_);
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
lean_dec_ref_known(v_t_14_, 3);
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
lean_dec_ref_known(v_t_14_, 6);
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
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(lean_object* v_x_61_){
_start:
{
if (lean_obj_tag(v_x_61_) == 0)
{
lean_object* v___x_62_; 
v___x_62_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0));
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
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(lean_object* v_x_81_){
_start:
{
if (lean_obj_tag(v_x_81_) == 0)
{
lean_object* v___x_82_; 
v___x_82_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0));
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
lean_dec_ref_known(v_x_105_, 5);
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
lean_dec_ref_known(v___x_119_, 1);
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
lean_dec_ref_known(v___x_138_, 1);
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
lean_dec_ref_known(v_x_154_, 1);
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
lean_dec_ref_known(v___x_228_, 1);
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
lean_dec_ref_known(v___x_239_, 1);
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
lean_dec_ref_known(v___x_251_, 1);
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
lean_dec_ref_known(v___x_263_, 1);
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
lean_dec_ref_known(v___x_275_, 1);
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
lean_dec_ref_known(v___x_287_, 1);
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
lean_dec_ref_known(v___x_299_, 1);
v___x_309_ = lean_unsigned_to_nat(5u);
v___x_310_ = lean_array_get_borrowed(v___x_231_, v_a_248_, v___x_309_);
lean_inc(v___x_310_);
v___x_311_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(v___x_310_);
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
lean_dec_ref_known(v___x_311_, 1);
v___x_321_ = lean_unsigned_to_nat(6u);
v___x_322_ = lean_array_get(v___x_231_, v_a_248_, v___x_321_);
lean_dec(v_a_248_);
v___x_323_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v___x_322_);
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
lean_dec_ref_known(v___x_344_, 1);
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
lean_dec_ref_known(v___x_356_, 1);
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
lean_dec_ref_known(v___x_368_, 1);
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
lean_dec_ref_known(v___x_380_, 1);
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
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__1(lean_object* v_x_413_){
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
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(lean_object* v_x_423_){
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
v___x_436_ = lean_panic_fn_borrowed(v___x_435_, v_msg_434_);
return v___x_436_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_440_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__2));
v___x_441_ = lean_unsigned_to_nat(35u);
v___x_442_ = lean_unsigned_to_nat(182u);
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
v___x_448_ = lean_unsigned_to_nat(183u);
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
v___x_456_ = lean_unsigned_to_nat(276u);
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
v___x_462_ = lean_unsigned_to_nat(277u);
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
lean_object* v_size_469_; lean_object* v_k_470_; lean_object* v_v_471_; lean_object* v_l_472_; lean_object* v_r_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_829_; 
v_size_469_ = lean_ctor_get(v_t_468_, 0);
v_k_470_ = lean_ctor_get(v_t_468_, 1);
v_v_471_ = lean_ctor_get(v_t_468_, 2);
v_l_472_ = lean_ctor_get(v_t_468_, 3);
v_r_473_ = lean_ctor_get(v_t_468_, 4);
v_isSharedCheck_829_ = !lean_is_exclusive(v_t_468_);
if (v_isSharedCheck_829_ == 0)
{
v___x_475_ = v_t_468_;
v_isShared_476_ = v_isSharedCheck_829_;
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
v_isShared_476_ = v_isSharedCheck_829_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
uint8_t v___x_477_; 
v___x_477_ = lean_string_compare(v_k_466_, v_k_470_);
switch(v___x_477_)
{
case 0:
{
lean_object* v___x_478_; 
lean_dec(v_size_469_);
v___x_478_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(v_k_466_, v_v_467_, v_l_472_);
if (lean_obj_tag(v_r_473_) == 0)
{
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_size_479_; lean_object* v_size_480_; lean_object* v_k_481_; lean_object* v_v_482_; lean_object* v_l_483_; lean_object* v_r_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v_size_479_ = lean_ctor_get(v_r_473_, 0);
v_size_480_ = lean_ctor_get(v___x_478_, 0);
v_k_481_ = lean_ctor_get(v___x_478_, 1);
v_v_482_ = lean_ctor_get(v___x_478_, 2);
v_l_483_ = lean_ctor_get(v___x_478_, 3);
v_r_484_ = lean_ctor_get(v___x_478_, 4);
lean_inc(v_r_484_);
v___x_485_ = lean_unsigned_to_nat(3u);
v___x_486_ = lean_nat_mul(v___x_485_, v_size_479_);
v___x_487_ = lean_nat_dec_lt(v___x_486_, v_size_480_);
lean_dec(v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
lean_dec(v_r_484_);
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = lean_nat_add(v___x_488_, v_size_480_);
v___x_490_ = lean_nat_add(v___x_489_, v_size_479_);
lean_dec(v___x_489_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 3, v___x_478_);
lean_ctor_set(v___x_475_, 0, v___x_490_);
v___x_492_ = v___x_475_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_493_, 3, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_493_, 4, v_r_473_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
else
{
lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_565_; 
lean_inc(v_l_483_);
lean_inc(v_v_482_);
lean_inc(v_k_481_);
lean_inc(v_size_480_);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_565_ == 0)
{
lean_object* v_unused_566_; lean_object* v_unused_567_; lean_object* v_unused_568_; lean_object* v_unused_569_; lean_object* v_unused_570_; 
v_unused_566_ = lean_ctor_get(v___x_478_, 4);
lean_dec(v_unused_566_);
v_unused_567_ = lean_ctor_get(v___x_478_, 3);
lean_dec(v_unused_567_);
v_unused_568_ = lean_ctor_get(v___x_478_, 2);
lean_dec(v_unused_568_);
v_unused_569_ = lean_ctor_get(v___x_478_, 1);
lean_dec(v_unused_569_);
v_unused_570_ = lean_ctor_get(v___x_478_, 0);
lean_dec(v_unused_570_);
v___x_495_ = v___x_478_;
v_isShared_496_ = v_isSharedCheck_565_;
goto v_resetjp_494_;
}
else
{
lean_dec(v___x_478_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_565_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
if (lean_obj_tag(v_l_483_) == 0)
{
if (lean_obj_tag(v_r_484_) == 0)
{
lean_object* v_size_497_; lean_object* v_size_498_; lean_object* v_k_499_; lean_object* v_v_500_; lean_object* v_l_501_; lean_object* v_r_502_; lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v_size_497_ = lean_ctor_get(v_l_483_, 0);
v_size_498_ = lean_ctor_get(v_r_484_, 0);
v_k_499_ = lean_ctor_get(v_r_484_, 1);
v_v_500_ = lean_ctor_get(v_r_484_, 2);
v_l_501_ = lean_ctor_get(v_r_484_, 3);
v_r_502_ = lean_ctor_get(v_r_484_, 4);
v___x_503_ = lean_unsigned_to_nat(2u);
v___x_504_ = lean_nat_mul(v___x_503_, v_size_497_);
v___x_505_ = lean_nat_dec_lt(v_size_498_, v___x_504_);
lean_dec(v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_535_; 
lean_inc(v_r_502_);
lean_inc(v_l_501_);
lean_inc(v_v_500_);
lean_inc(v_k_499_);
v_isSharedCheck_535_ = !lean_is_exclusive(v_r_484_);
if (v_isSharedCheck_535_ == 0)
{
lean_object* v_unused_536_; lean_object* v_unused_537_; lean_object* v_unused_538_; lean_object* v_unused_539_; lean_object* v_unused_540_; 
v_unused_536_ = lean_ctor_get(v_r_484_, 4);
lean_dec(v_unused_536_);
v_unused_537_ = lean_ctor_get(v_r_484_, 3);
lean_dec(v_unused_537_);
v_unused_538_ = lean_ctor_get(v_r_484_, 2);
lean_dec(v_unused_538_);
v_unused_539_ = lean_ctor_get(v_r_484_, 1);
lean_dec(v_unused_539_);
v_unused_540_ = lean_ctor_get(v_r_484_, 0);
lean_dec(v_unused_540_);
v___x_507_ = v_r_484_;
v_isShared_508_ = v_isSharedCheck_535_;
goto v_resetjp_506_;
}
else
{
lean_dec(v_r_484_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_535_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___x_523_; lean_object* v___y_525_; 
v___x_509_ = lean_unsigned_to_nat(1u);
v___x_510_ = lean_nat_add(v___x_509_, v_size_480_);
lean_dec(v_size_480_);
v___x_511_ = lean_nat_add(v___x_510_, v_size_479_);
lean_dec(v___x_510_);
v___x_523_ = lean_nat_add(v___x_509_, v_size_497_);
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
v___jp_512_:
{
lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_516_ = lean_nat_add(v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec(v___y_514_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 4, v_r_473_);
lean_ctor_set(v___x_507_, 3, v_r_502_);
lean_ctor_set(v___x_507_, 2, v_v_471_);
lean_ctor_set(v___x_507_, 1, v_k_470_);
lean_ctor_set(v___x_507_, 0, v___x_516_);
v___x_518_ = v___x_507_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_522_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_522_, 3, v_r_502_);
lean_ctor_set(v_reuseFailAlloc_522_, 4, v_r_473_);
v___x_518_ = v_reuseFailAlloc_522_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_520_; 
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 4, v___x_518_);
lean_ctor_set(v___x_495_, 3, v___y_513_);
lean_ctor_set(v___x_495_, 2, v_v_500_);
lean_ctor_set(v___x_495_, 1, v_k_499_);
lean_ctor_set(v___x_495_, 0, v___x_511_);
v___x_520_ = v___x_495_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_k_499_);
lean_ctor_set(v_reuseFailAlloc_521_, 2, v_v_500_);
lean_ctor_set(v_reuseFailAlloc_521_, 3, v___y_513_);
lean_ctor_set(v_reuseFailAlloc_521_, 4, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
v___jp_524_:
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = lean_nat_add(v___x_523_, v___y_525_);
lean_dec(v___y_525_);
lean_dec(v___x_523_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v_l_501_);
lean_ctor_set(v___x_475_, 3, v_l_483_);
lean_ctor_set(v___x_475_, 2, v_v_482_);
lean_ctor_set(v___x_475_, 1, v_k_481_);
lean_ctor_set(v___x_475_, 0, v___x_526_);
v___x_528_ = v___x_475_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_k_481_);
lean_ctor_set(v_reuseFailAlloc_532_, 2, v_v_482_);
lean_ctor_set(v_reuseFailAlloc_532_, 3, v_l_483_);
lean_ctor_set(v_reuseFailAlloc_532_, 4, v_l_501_);
v___x_528_ = v_reuseFailAlloc_532_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_529_; 
v___x_529_ = lean_nat_add(v___x_509_, v_size_479_);
if (lean_obj_tag(v_r_502_) == 0)
{
lean_object* v_size_530_; 
v_size_530_ = lean_ctor_get(v_r_502_, 0);
lean_inc(v_size_530_);
v___y_513_ = v___x_528_;
v___y_514_ = v___x_529_;
v___y_515_ = v_size_530_;
goto v___jp_512_;
}
else
{
lean_object* v___x_531_; 
v___x_531_ = lean_unsigned_to_nat(0u);
v___y_513_ = v___x_528_;
v___y_514_ = v___x_529_;
v___y_515_ = v___x_531_;
goto v___jp_512_;
}
}
}
}
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_547_; 
lean_del_object(v___x_475_);
v___x_541_ = lean_unsigned_to_nat(1u);
v___x_542_ = lean_nat_add(v___x_541_, v_size_480_);
lean_dec(v_size_480_);
v___x_543_ = lean_nat_add(v___x_542_, v_size_479_);
lean_dec(v___x_542_);
v___x_544_ = lean_nat_add(v___x_541_, v_size_479_);
v___x_545_ = lean_nat_add(v___x_544_, v_size_498_);
lean_dec(v___x_544_);
lean_inc_ref(v_r_473_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 4, v_r_473_);
lean_ctor_set(v___x_495_, 3, v_r_484_);
lean_ctor_set(v___x_495_, 2, v_v_471_);
lean_ctor_set(v___x_495_, 1, v_k_470_);
lean_ctor_set(v___x_495_, 0, v___x_545_);
v___x_547_ = v___x_495_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_560_, 3, v_r_484_);
lean_ctor_set(v_reuseFailAlloc_560_, 4, v_r_473_);
v___x_547_ = v_reuseFailAlloc_560_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_isSharedCheck_554_ = !lean_is_exclusive(v_r_473_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; lean_object* v_unused_556_; lean_object* v_unused_557_; lean_object* v_unused_558_; lean_object* v_unused_559_; 
v_unused_555_ = lean_ctor_get(v_r_473_, 4);
lean_dec(v_unused_555_);
v_unused_556_ = lean_ctor_get(v_r_473_, 3);
lean_dec(v_unused_556_);
v_unused_557_ = lean_ctor_get(v_r_473_, 2);
lean_dec(v_unused_557_);
v_unused_558_ = lean_ctor_get(v_r_473_, 1);
lean_dec(v_unused_558_);
v_unused_559_ = lean_ctor_get(v_r_473_, 0);
lean_dec(v_unused_559_);
v___x_549_ = v_r_473_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_dec(v_r_473_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 4, v___x_547_);
lean_ctor_set(v___x_549_, 3, v_l_483_);
lean_ctor_set(v___x_549_, 2, v_v_482_);
lean_ctor_set(v___x_549_, 1, v_k_481_);
lean_ctor_set(v___x_549_, 0, v___x_543_);
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_k_481_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v_v_482_);
lean_ctor_set(v_reuseFailAlloc_553_, 3, v_l_483_);
lean_ctor_set(v_reuseFailAlloc_553_, 4, v___x_547_);
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
lean_dec_ref_known(v_l_483_, 5);
lean_del_object(v___x_495_);
lean_dec(v_v_482_);
lean_dec(v_k_481_);
lean_dec(v_size_480_);
lean_dec_ref_known(v_r_473_, 5);
lean_del_object(v___x_475_);
lean_dec(v_v_471_);
lean_dec(v_k_470_);
v___x_561_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3);
v___x_562_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v___x_561_);
return v___x_562_;
}
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_del_object(v___x_495_);
lean_dec(v_r_484_);
lean_dec(v_v_482_);
lean_dec(v_k_481_);
lean_dec(v_size_480_);
lean_dec_ref_known(v_r_473_, 5);
lean_del_object(v___x_475_);
lean_dec(v_v_471_);
lean_dec(v_k_470_);
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
v_size_571_ = lean_ctor_get(v_r_473_, 0);
v___x_572_ = lean_unsigned_to_nat(1u);
v___x_573_ = lean_nat_add(v___x_572_, v_size_571_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 3, v___x_478_);
lean_ctor_set(v___x_475_, 0, v___x_573_);
v___x_575_ = v___x_475_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_576_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_576_, 3, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_576_, 4, v_r_473_);
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
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_l_577_; 
v_l_577_ = lean_ctor_get(v___x_478_, 3);
if (lean_obj_tag(v_l_577_) == 0)
{
lean_object* v_r_578_; 
lean_inc_ref(v_l_577_);
v_r_578_ = lean_ctor_get(v___x_478_, 4);
lean_inc(v_r_578_);
if (lean_obj_tag(v_r_578_) == 0)
{
lean_object* v_size_579_; lean_object* v_k_580_; lean_object* v_v_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_595_; 
v_size_579_ = lean_ctor_get(v___x_478_, 0);
v_k_580_ = lean_ctor_get(v___x_478_, 1);
v_v_581_ = lean_ctor_get(v___x_478_, 2);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; lean_object* v_unused_597_; 
v_unused_596_ = lean_ctor_get(v___x_478_, 4);
lean_dec(v_unused_596_);
v_unused_597_ = lean_ctor_get(v___x_478_, 3);
lean_dec(v_unused_597_);
v___x_583_ = v___x_478_;
v_isShared_584_ = v_isSharedCheck_595_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_v_581_);
lean_inc(v_k_580_);
lean_inc(v_size_579_);
lean_dec(v___x_478_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_595_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v_size_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
v_size_585_ = lean_ctor_get(v_r_578_, 0);
v___x_586_ = lean_unsigned_to_nat(1u);
v___x_587_ = lean_nat_add(v___x_586_, v_size_579_);
lean_dec(v_size_579_);
v___x_588_ = lean_nat_add(v___x_586_, v_size_585_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 4, v_r_473_);
lean_ctor_set(v___x_583_, 3, v_r_578_);
lean_ctor_set(v___x_583_, 2, v_v_471_);
lean_ctor_set(v___x_583_, 1, v_k_470_);
lean_ctor_set(v___x_583_, 0, v___x_588_);
v___x_590_ = v___x_583_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_594_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_594_, 3, v_r_578_);
lean_ctor_set(v_reuseFailAlloc_594_, 4, v_r_473_);
v___x_590_ = v_reuseFailAlloc_594_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_592_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v___x_590_);
lean_ctor_set(v___x_475_, 3, v_l_577_);
lean_ctor_set(v___x_475_, 2, v_v_581_);
lean_ctor_set(v___x_475_, 1, v_k_580_);
lean_ctor_set(v___x_475_, 0, v___x_587_);
v___x_592_ = v___x_475_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_k_580_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v_v_581_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v_l_577_);
lean_ctor_set(v_reuseFailAlloc_593_, 4, v___x_590_);
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
lean_object* v_k_598_; lean_object* v_v_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_611_; 
v_k_598_ = lean_ctor_get(v___x_478_, 1);
v_v_599_ = lean_ctor_get(v___x_478_, 2);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; lean_object* v_unused_613_; lean_object* v_unused_614_; 
v_unused_612_ = lean_ctor_get(v___x_478_, 4);
lean_dec(v_unused_612_);
v_unused_613_ = lean_ctor_get(v___x_478_, 3);
lean_dec(v_unused_613_);
v_unused_614_ = lean_ctor_get(v___x_478_, 0);
lean_dec(v_unused_614_);
v___x_601_ = v___x_478_;
v_isShared_602_ = v_isSharedCheck_611_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_v_599_);
lean_inc(v_k_598_);
lean_dec(v___x_478_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_611_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_603_ = lean_unsigned_to_nat(3u);
v___x_604_ = lean_unsigned_to_nat(1u);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 3, v_r_578_);
lean_ctor_set(v___x_601_, 2, v_v_471_);
lean_ctor_set(v___x_601_, 1, v_k_470_);
lean_ctor_set(v___x_601_, 0, v___x_604_);
v___x_606_ = v___x_601_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_610_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_610_, 3, v_r_578_);
lean_ctor_set(v_reuseFailAlloc_610_, 4, v_r_578_);
v___x_606_ = v_reuseFailAlloc_610_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_608_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v___x_606_);
lean_ctor_set(v___x_475_, 3, v_l_577_);
lean_ctor_set(v___x_475_, 2, v_v_599_);
lean_ctor_set(v___x_475_, 1, v_k_598_);
lean_ctor_set(v___x_475_, 0, v___x_603_);
v___x_608_ = v___x_475_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_k_598_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v_v_599_);
lean_ctor_set(v_reuseFailAlloc_609_, 3, v_l_577_);
lean_ctor_set(v_reuseFailAlloc_609_, 4, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
else
{
lean_object* v_r_615_; 
v_r_615_ = lean_ctor_get(v___x_478_, 4);
lean_inc(v_r_615_);
if (lean_obj_tag(v_r_615_) == 0)
{
lean_object* v_k_616_; lean_object* v_v_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_641_; 
lean_inc(v_l_577_);
v_k_616_ = lean_ctor_get(v___x_478_, 1);
v_v_617_ = lean_ctor_get(v___x_478_, 2);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; lean_object* v_unused_643_; lean_object* v_unused_644_; 
v_unused_642_ = lean_ctor_get(v___x_478_, 4);
lean_dec(v_unused_642_);
v_unused_643_ = lean_ctor_get(v___x_478_, 3);
lean_dec(v_unused_643_);
v_unused_644_ = lean_ctor_get(v___x_478_, 0);
lean_dec(v_unused_644_);
v___x_619_ = v___x_478_;
v_isShared_620_ = v_isSharedCheck_641_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_v_617_);
lean_inc(v_k_616_);
lean_dec(v___x_478_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_641_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v_k_621_; lean_object* v_v_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_637_; 
v_k_621_ = lean_ctor_get(v_r_615_, 1);
v_v_622_ = lean_ctor_get(v_r_615_, 2);
v_isSharedCheck_637_ = !lean_is_exclusive(v_r_615_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; lean_object* v_unused_639_; lean_object* v_unused_640_; 
v_unused_638_ = lean_ctor_get(v_r_615_, 4);
lean_dec(v_unused_638_);
v_unused_639_ = lean_ctor_get(v_r_615_, 3);
lean_dec(v_unused_639_);
v_unused_640_ = lean_ctor_get(v_r_615_, 0);
lean_dec(v_unused_640_);
v___x_624_ = v_r_615_;
v_isShared_625_ = v_isSharedCheck_637_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_v_622_);
lean_inc(v_k_621_);
lean_dec(v_r_615_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_637_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_626_ = lean_unsigned_to_nat(3u);
v___x_627_ = lean_unsigned_to_nat(1u);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 4, v_l_577_);
lean_ctor_set(v___x_624_, 3, v_l_577_);
lean_ctor_set(v___x_624_, 2, v_v_617_);
lean_ctor_set(v___x_624_, 1, v_k_616_);
lean_ctor_set(v___x_624_, 0, v___x_627_);
v___x_629_ = v___x_624_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_k_616_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_v_617_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v_l_577_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v_l_577_);
v___x_629_ = v_reuseFailAlloc_636_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_631_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 4, v_l_577_);
lean_ctor_set(v___x_619_, 2, v_v_471_);
lean_ctor_set(v___x_619_, 1, v_k_470_);
lean_ctor_set(v___x_619_, 0, v___x_627_);
v___x_631_ = v___x_619_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_635_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_635_, 3, v_l_577_);
lean_ctor_set(v_reuseFailAlloc_635_, 4, v_l_577_);
v___x_631_ = v_reuseFailAlloc_635_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_633_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v___x_631_);
lean_ctor_set(v___x_475_, 3, v___x_629_);
lean_ctor_set(v___x_475_, 2, v_v_622_);
lean_ctor_set(v___x_475_, 1, v_k_621_);
lean_ctor_set(v___x_475_, 0, v___x_626_);
v___x_633_ = v___x_475_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_k_621_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v_v_622_);
lean_ctor_set(v_reuseFailAlloc_634_, 3, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_634_, 4, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
}
else
{
lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_645_ = lean_unsigned_to_nat(2u);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v_r_615_);
lean_ctor_set(v___x_475_, 3, v___x_478_);
lean_ctor_set(v___x_475_, 0, v___x_645_);
v___x_647_ = v___x_475_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_648_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_648_, 3, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_648_, 4, v_r_615_);
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
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v___x_478_);
lean_ctor_set(v___x_475_, 3, v___x_478_);
lean_ctor_set(v___x_475_, 0, v___x_649_);
v___x_651_ = v___x_475_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_652_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_652_, 3, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_652_, 4, v___x_478_);
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
case 1:
{
lean_object* v___x_654_; 
lean_dec(v_v_471_);
lean_dec(v_k_470_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 2, v_v_467_);
lean_ctor_set(v___x_475_, 1, v_k_466_);
v___x_654_ = v___x_475_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_size_469_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_k_466_);
lean_ctor_set(v_reuseFailAlloc_655_, 2, v_v_467_);
lean_ctor_set(v_reuseFailAlloc_655_, 3, v_l_472_);
lean_ctor_set(v_reuseFailAlloc_655_, 4, v_r_473_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
default: 
{
lean_object* v___x_656_; 
lean_dec(v_size_469_);
v___x_656_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(v_k_466_, v_v_467_, v_r_473_);
if (lean_obj_tag(v_l_472_) == 0)
{
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_size_657_; lean_object* v_size_658_; lean_object* v_k_659_; lean_object* v_v_660_; lean_object* v_l_661_; lean_object* v_r_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v_size_657_ = lean_ctor_get(v_l_472_, 0);
v_size_658_ = lean_ctor_get(v___x_656_, 0);
v_k_659_ = lean_ctor_get(v___x_656_, 1);
v_v_660_ = lean_ctor_get(v___x_656_, 2);
v_l_661_ = lean_ctor_get(v___x_656_, 3);
lean_inc(v_l_661_);
v_r_662_ = lean_ctor_get(v___x_656_, 4);
v___x_663_ = lean_unsigned_to_nat(3u);
v___x_664_ = lean_nat_mul(v___x_663_, v_size_657_);
v___x_665_ = lean_nat_dec_lt(v___x_664_, v_size_658_);
lean_dec(v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
lean_dec(v_l_661_);
v___x_666_ = lean_unsigned_to_nat(1u);
v___x_667_ = lean_nat_add(v___x_666_, v_size_657_);
v___x_668_ = lean_nat_add(v___x_667_, v_size_658_);
lean_dec(v___x_667_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v___x_656_);
lean_ctor_set(v___x_475_, 0, v___x_668_);
v___x_670_ = v___x_475_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_671_, 3, v_l_472_);
lean_ctor_set(v_reuseFailAlloc_671_, 4, v___x_656_);
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
lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_741_; 
lean_inc(v_r_662_);
lean_inc(v_v_660_);
lean_inc(v_k_659_);
lean_inc(v_size_658_);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; lean_object* v_unused_743_; lean_object* v_unused_744_; lean_object* v_unused_745_; lean_object* v_unused_746_; 
v_unused_742_ = lean_ctor_get(v___x_656_, 4);
lean_dec(v_unused_742_);
v_unused_743_ = lean_ctor_get(v___x_656_, 3);
lean_dec(v_unused_743_);
v_unused_744_ = lean_ctor_get(v___x_656_, 2);
lean_dec(v_unused_744_);
v_unused_745_ = lean_ctor_get(v___x_656_, 1);
lean_dec(v_unused_745_);
v_unused_746_ = lean_ctor_get(v___x_656_, 0);
lean_dec(v_unused_746_);
v___x_673_ = v___x_656_;
v_isShared_674_ = v_isSharedCheck_741_;
goto v_resetjp_672_;
}
else
{
lean_dec(v___x_656_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_741_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
if (lean_obj_tag(v_l_661_) == 0)
{
if (lean_obj_tag(v_r_662_) == 0)
{
lean_object* v_size_675_; lean_object* v_k_676_; lean_object* v_v_677_; lean_object* v_l_678_; lean_object* v_r_679_; lean_object* v_size_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v_size_675_ = lean_ctor_get(v_l_661_, 0);
v_k_676_ = lean_ctor_get(v_l_661_, 1);
v_v_677_ = lean_ctor_get(v_l_661_, 2);
v_l_678_ = lean_ctor_get(v_l_661_, 3);
v_r_679_ = lean_ctor_get(v_l_661_, 4);
v_size_680_ = lean_ctor_get(v_r_662_, 0);
v___x_681_ = lean_unsigned_to_nat(2u);
v___x_682_ = lean_nat_mul(v___x_681_, v_size_680_);
v___x_683_ = lean_nat_dec_lt(v_size_675_, v___x_682_);
lean_dec(v___x_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_712_; 
lean_inc(v_r_679_);
lean_inc(v_l_678_);
lean_inc(v_v_677_);
lean_inc(v_k_676_);
v_isSharedCheck_712_ = !lean_is_exclusive(v_l_661_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; lean_object* v_unused_714_; lean_object* v_unused_715_; lean_object* v_unused_716_; lean_object* v_unused_717_; 
v_unused_713_ = lean_ctor_get(v_l_661_, 4);
lean_dec(v_unused_713_);
v_unused_714_ = lean_ctor_get(v_l_661_, 3);
lean_dec(v_unused_714_);
v_unused_715_ = lean_ctor_get(v_l_661_, 2);
lean_dec(v_unused_715_);
v_unused_716_ = lean_ctor_get(v_l_661_, 1);
lean_dec(v_unused_716_);
v_unused_717_ = lean_ctor_get(v_l_661_, 0);
lean_dec(v_unused_717_);
v___x_685_ = v_l_661_;
v_isShared_686_ = v_isSharedCheck_712_;
goto v_resetjp_684_;
}
else
{
lean_dec(v_l_661_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_712_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_702_; 
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = lean_nat_add(v___x_687_, v_size_657_);
v___x_689_ = lean_nat_add(v___x_688_, v_size_658_);
lean_dec(v_size_658_);
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
v___jp_690_:
{
lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_694_ = lean_nat_add(v___y_692_, v___y_693_);
lean_dec(v___y_693_);
lean_dec(v___y_692_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 4, v_r_662_);
lean_ctor_set(v___x_685_, 3, v_r_679_);
lean_ctor_set(v___x_685_, 2, v_v_660_);
lean_ctor_set(v___x_685_, 1, v_k_659_);
lean_ctor_set(v___x_685_, 0, v___x_694_);
v___x_696_ = v___x_685_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v_r_679_);
lean_ctor_set(v_reuseFailAlloc_700_, 4, v_r_662_);
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
lean_ctor_set(v___x_673_, 2, v_v_677_);
lean_ctor_set(v___x_673_, 1, v_k_676_);
lean_ctor_set(v___x_673_, 0, v___x_689_);
v___x_698_ = v___x_673_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_k_676_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v_v_677_);
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
v___jp_701_:
{
lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_703_ = lean_nat_add(v___x_688_, v___y_702_);
lean_dec(v___y_702_);
lean_dec(v___x_688_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v_l_678_);
lean_ctor_set(v___x_475_, 0, v___x_703_);
v___x_705_ = v___x_475_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_709_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_709_, 3, v_l_472_);
lean_ctor_set(v_reuseFailAlloc_709_, 4, v_l_678_);
v___x_705_ = v_reuseFailAlloc_709_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_706_; 
v___x_706_ = lean_nat_add(v___x_687_, v_size_680_);
if (lean_obj_tag(v_r_679_) == 0)
{
lean_object* v_size_707_; 
v_size_707_ = lean_ctor_get(v_r_679_, 0);
lean_inc(v_size_707_);
v___y_691_ = v___x_705_;
v___y_692_ = v___x_706_;
v___y_693_ = v_size_707_;
goto v___jp_690_;
}
else
{
lean_object* v___x_708_; 
v___x_708_ = lean_unsigned_to_nat(0u);
v___y_691_ = v___x_705_;
v___y_692_ = v___x_706_;
v___y_693_ = v___x_708_;
goto v___jp_690_;
}
}
}
}
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
lean_del_object(v___x_475_);
v___x_718_ = lean_unsigned_to_nat(1u);
v___x_719_ = lean_nat_add(v___x_718_, v_size_657_);
v___x_720_ = lean_nat_add(v___x_719_, v_size_658_);
lean_dec(v_size_658_);
v___x_721_ = lean_nat_add(v___x_719_, v_size_675_);
lean_dec(v___x_719_);
lean_inc_ref(v_l_472_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 4, v_l_661_);
lean_ctor_set(v___x_673_, 3, v_l_472_);
lean_ctor_set(v___x_673_, 2, v_v_471_);
lean_ctor_set(v___x_673_, 1, v_k_470_);
lean_ctor_set(v___x_673_, 0, v___x_721_);
v___x_723_ = v___x_673_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_736_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_736_, 3, v_l_472_);
lean_ctor_set(v_reuseFailAlloc_736_, 4, v_l_661_);
v___x_723_ = v_reuseFailAlloc_736_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
v_isSharedCheck_730_ = !lean_is_exclusive(v_l_472_);
if (v_isSharedCheck_730_ == 0)
{
lean_object* v_unused_731_; lean_object* v_unused_732_; lean_object* v_unused_733_; lean_object* v_unused_734_; lean_object* v_unused_735_; 
v_unused_731_ = lean_ctor_get(v_l_472_, 4);
lean_dec(v_unused_731_);
v_unused_732_ = lean_ctor_get(v_l_472_, 3);
lean_dec(v_unused_732_);
v_unused_733_ = lean_ctor_get(v_l_472_, 2);
lean_dec(v_unused_733_);
v_unused_734_ = lean_ctor_get(v_l_472_, 1);
lean_dec(v_unused_734_);
v_unused_735_ = lean_ctor_get(v_l_472_, 0);
lean_dec(v_unused_735_);
v___x_725_ = v_l_472_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_dec(v_l_472_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 4, v_r_662_);
lean_ctor_set(v___x_725_, 3, v___x_723_);
lean_ctor_set(v___x_725_, 2, v_v_660_);
lean_ctor_set(v___x_725_, 1, v_k_659_);
lean_ctor_set(v___x_725_, 0, v___x_720_);
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_729_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_729_, 3, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_729_, 4, v_r_662_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; 
lean_dec_ref_known(v_l_661_, 5);
lean_del_object(v___x_673_);
lean_dec(v_v_660_);
lean_dec(v_k_659_);
lean_dec(v_size_658_);
lean_dec_ref_known(v_l_472_, 5);
lean_del_object(v___x_475_);
lean_dec(v_v_471_);
lean_dec(v_k_470_);
v___x_737_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7);
v___x_738_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v___x_737_);
return v___x_738_;
}
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; 
lean_del_object(v___x_673_);
lean_dec(v_r_662_);
lean_dec(v_v_660_);
lean_dec(v_k_659_);
lean_dec(v_size_658_);
lean_dec_ref_known(v_l_472_, 5);
lean_del_object(v___x_475_);
lean_dec(v_v_471_);
lean_dec(v_k_470_);
v___x_739_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8);
v___x_740_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v___x_739_);
return v___x_740_;
}
}
}
}
else
{
lean_object* v_size_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
v_size_747_ = lean_ctor_get(v_l_472_, 0);
v___x_748_ = lean_unsigned_to_nat(1u);
v___x_749_ = lean_nat_add(v___x_748_, v_size_747_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v___x_656_);
lean_ctor_set(v___x_475_, 0, v___x_749_);
v___x_751_ = v___x_475_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_752_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_752_, 3, v_l_472_);
lean_ctor_set(v_reuseFailAlloc_752_, 4, v___x_656_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
else
{
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_l_753_; 
v_l_753_ = lean_ctor_get(v___x_656_, 3);
lean_inc(v_l_753_);
if (lean_obj_tag(v_l_753_) == 0)
{
lean_object* v_r_754_; 
v_r_754_ = lean_ctor_get(v___x_656_, 4);
lean_inc(v_r_754_);
if (lean_obj_tag(v_r_754_) == 0)
{
lean_object* v_size_755_; lean_object* v_k_756_; lean_object* v_v_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_771_; 
v_size_755_ = lean_ctor_get(v___x_656_, 0);
v_k_756_ = lean_ctor_get(v___x_656_, 1);
v_v_757_ = lean_ctor_get(v___x_656_, 2);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; lean_object* v_unused_773_; 
v_unused_772_ = lean_ctor_get(v___x_656_, 4);
lean_dec(v_unused_772_);
v_unused_773_ = lean_ctor_get(v___x_656_, 3);
lean_dec(v_unused_773_);
v___x_759_ = v___x_656_;
v_isShared_760_ = v_isSharedCheck_771_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_v_757_);
lean_inc(v_k_756_);
lean_inc(v_size_755_);
lean_dec(v___x_656_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_771_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v_size_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v_size_761_ = lean_ctor_get(v_l_753_, 0);
v___x_762_ = lean_unsigned_to_nat(1u);
v___x_763_ = lean_nat_add(v___x_762_, v_size_755_);
lean_dec(v_size_755_);
v___x_764_ = lean_nat_add(v___x_762_, v_size_761_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 4, v_l_753_);
lean_ctor_set(v___x_759_, 3, v_l_472_);
lean_ctor_set(v___x_759_, 2, v_v_471_);
lean_ctor_set(v___x_759_, 1, v_k_470_);
lean_ctor_set(v___x_759_, 0, v___x_764_);
v___x_766_ = v___x_759_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v_l_472_);
lean_ctor_set(v_reuseFailAlloc_770_, 4, v_l_753_);
v___x_766_ = v_reuseFailAlloc_770_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_768_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v_r_754_);
lean_ctor_set(v___x_475_, 3, v___x_766_);
lean_ctor_set(v___x_475_, 2, v_v_757_);
lean_ctor_set(v___x_475_, 1, v_k_756_);
lean_ctor_set(v___x_475_, 0, v___x_763_);
v___x_768_ = v___x_475_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_k_756_);
lean_ctor_set(v_reuseFailAlloc_769_, 2, v_v_757_);
lean_ctor_set(v_reuseFailAlloc_769_, 3, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_769_, 4, v_r_754_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_object* v_k_774_; lean_object* v_v_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_799_; 
v_k_774_ = lean_ctor_get(v___x_656_, 1);
v_v_775_ = lean_ctor_get(v___x_656_, 2);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_799_ == 0)
{
lean_object* v_unused_800_; lean_object* v_unused_801_; lean_object* v_unused_802_; 
v_unused_800_ = lean_ctor_get(v___x_656_, 4);
lean_dec(v_unused_800_);
v_unused_801_ = lean_ctor_get(v___x_656_, 3);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v___x_656_, 0);
lean_dec(v_unused_802_);
v___x_777_ = v___x_656_;
v_isShared_778_ = v_isSharedCheck_799_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_v_775_);
lean_inc(v_k_774_);
lean_dec(v___x_656_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_799_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v_k_779_; lean_object* v_v_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_795_; 
v_k_779_ = lean_ctor_get(v_l_753_, 1);
v_v_780_ = lean_ctor_get(v_l_753_, 2);
v_isSharedCheck_795_ = !lean_is_exclusive(v_l_753_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; lean_object* v_unused_797_; lean_object* v_unused_798_; 
v_unused_796_ = lean_ctor_get(v_l_753_, 4);
lean_dec(v_unused_796_);
v_unused_797_ = lean_ctor_get(v_l_753_, 3);
lean_dec(v_unused_797_);
v_unused_798_ = lean_ctor_get(v_l_753_, 0);
lean_dec(v_unused_798_);
v___x_782_ = v_l_753_;
v_isShared_783_ = v_isSharedCheck_795_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_v_780_);
lean_inc(v_k_779_);
lean_dec(v_l_753_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_795_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
v___x_784_ = lean_unsigned_to_nat(3u);
v___x_785_ = lean_unsigned_to_nat(1u);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 4, v_r_754_);
lean_ctor_set(v___x_782_, 3, v_r_754_);
lean_ctor_set(v___x_782_, 2, v_v_471_);
lean_ctor_set(v___x_782_, 1, v_k_470_);
lean_ctor_set(v___x_782_, 0, v___x_785_);
v___x_787_ = v___x_782_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_794_, 3, v_r_754_);
lean_ctor_set(v_reuseFailAlloc_794_, 4, v_r_754_);
v___x_787_ = v_reuseFailAlloc_794_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_789_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 3, v_r_754_);
lean_ctor_set(v___x_777_, 0, v___x_785_);
v___x_789_ = v___x_777_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_k_774_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v_v_775_);
lean_ctor_set(v_reuseFailAlloc_793_, 3, v_r_754_);
lean_ctor_set(v_reuseFailAlloc_793_, 4, v_r_754_);
v___x_789_ = v_reuseFailAlloc_793_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_791_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v___x_789_);
lean_ctor_set(v___x_475_, 3, v___x_787_);
lean_ctor_set(v___x_475_, 2, v_v_780_);
lean_ctor_set(v___x_475_, 1, v_k_779_);
lean_ctor_set(v___x_475_, 0, v___x_784_);
v___x_791_ = v___x_475_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_k_779_);
lean_ctor_set(v_reuseFailAlloc_792_, 2, v_v_780_);
lean_ctor_set(v_reuseFailAlloc_792_, 3, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_792_, 4, v___x_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_803_; 
v_r_803_ = lean_ctor_get(v___x_656_, 4);
lean_inc(v_r_803_);
if (lean_obj_tag(v_r_803_) == 0)
{
lean_object* v_k_804_; lean_object* v_v_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_817_; 
v_k_804_ = lean_ctor_get(v___x_656_, 1);
v_v_805_ = lean_ctor_get(v___x_656_, 2);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; lean_object* v_unused_819_; lean_object* v_unused_820_; 
v_unused_818_ = lean_ctor_get(v___x_656_, 4);
lean_dec(v_unused_818_);
v_unused_819_ = lean_ctor_get(v___x_656_, 3);
lean_dec(v_unused_819_);
v_unused_820_ = lean_ctor_get(v___x_656_, 0);
lean_dec(v_unused_820_);
v___x_807_ = v___x_656_;
v_isShared_808_ = v_isSharedCheck_817_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_v_805_);
lean_inc(v_k_804_);
lean_dec(v___x_656_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_817_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_809_ = lean_unsigned_to_nat(3u);
v___x_810_ = lean_unsigned_to_nat(1u);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 4, v_l_753_);
lean_ctor_set(v___x_807_, 2, v_v_471_);
lean_ctor_set(v___x_807_, 1, v_k_470_);
lean_ctor_set(v___x_807_, 0, v___x_810_);
v___x_812_ = v___x_807_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_816_, 3, v_l_753_);
lean_ctor_set(v_reuseFailAlloc_816_, 4, v_l_753_);
v___x_812_ = v_reuseFailAlloc_816_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_814_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v_r_803_);
lean_ctor_set(v___x_475_, 3, v___x_812_);
lean_ctor_set(v___x_475_, 2, v_v_805_);
lean_ctor_set(v___x_475_, 1, v_k_804_);
lean_ctor_set(v___x_475_, 0, v___x_809_);
v___x_814_ = v___x_475_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_k_804_);
lean_ctor_set(v_reuseFailAlloc_815_, 2, v_v_805_);
lean_ctor_set(v_reuseFailAlloc_815_, 3, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_815_, 4, v_r_803_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
else
{
lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_821_ = lean_unsigned_to_nat(2u);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v___x_656_);
lean_ctor_set(v___x_475_, 3, v_r_803_);
lean_ctor_set(v___x_475_, 0, v___x_821_);
v___x_823_ = v___x_475_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_824_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_824_, 3, v_r_803_);
lean_ctor_set(v_reuseFailAlloc_824_, 4, v___x_656_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
else
{
lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_825_ = lean_unsigned_to_nat(1u);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 4, v___x_656_);
lean_ctor_set(v___x_475_, 3, v___x_656_);
lean_ctor_set(v___x_475_, 0, v___x_825_);
v___x_827_ = v___x_475_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_k_470_);
lean_ctor_set(v_reuseFailAlloc_828_, 2, v_v_471_);
lean_ctor_set(v_reuseFailAlloc_828_, 3, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_828_, 4, v___x_656_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_unsigned_to_nat(1u);
v___x_831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set(v___x_831_, 1, v_k_466_);
lean_ctor_set(v___x_831_, 2, v_v_467_);
lean_ctor_set(v___x_831_, 3, v_t_468_);
lean_ctor_set(v___x_831_, 4, v_t_468_);
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1_spec__5(lean_object* v_init_832_, lean_object* v_x_833_){
_start:
{
if (lean_obj_tag(v_x_833_) == 0)
{
lean_object* v_k_834_; lean_object* v_v_835_; lean_object* v_l_836_; lean_object* v_r_837_; lean_object* v___x_838_; uint8_t v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_k_834_ = lean_ctor_get(v_x_833_, 1);
lean_inc(v_k_834_);
v_v_835_ = lean_ctor_get(v_x_833_, 2);
lean_inc(v_v_835_);
v_l_836_ = lean_ctor_get(v_x_833_, 3);
lean_inc(v_l_836_);
v_r_837_ = lean_ctor_get(v_x_833_, 4);
lean_inc(v_r_837_);
lean_dec_ref_known(v_x_833_, 5);
v___x_838_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1_spec__5(v_init_832_, v_l_836_);
v___x_839_ = 1;
v___x_840_ = l_Lean_Name_toString(v_k_834_, v___x_839_);
v___x_841_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_841_, 0, v_v_835_);
v___x_842_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(v___x_840_, v___x_841_, v___x_838_);
v_init_832_ = v___x_842_;
v_x_833_ = v_r_837_;
goto _start;
}
else
{
return v_init_832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0(lean_object* v_m_844_){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_845_ = lean_box(1);
v___x_846_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1_spec__5(v___x_845_, v_m_844_);
v___x_847_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson(lean_object* v_x_848_){
_start:
{
if (lean_obj_tag(v_x_848_) == 0)
{
lean_object* v_name_849_; lean_object* v_opts_850_; uint8_t v_inherited_851_; lean_object* v_dir_852_; lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_name_849_ = lean_ctor_get(v_x_848_, 0);
lean_inc(v_name_849_);
v_opts_850_ = lean_ctor_get(v_x_848_, 1);
lean_inc(v_opts_850_);
v_inherited_851_ = lean_ctor_get_uint8(v_x_848_, sizeof(void*)*3);
v_dir_852_ = lean_ctor_get(v_x_848_, 2);
lean_inc_ref(v_dir_852_);
lean_dec_ref_known(v_x_848_, 3);
v___x_853_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2));
v___x_854_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_855_ = 1;
v___x_856_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_849_, v___x_855_);
v___x_857_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_854_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__8));
v___x_860_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0(v_opts_850_);
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10));
v___x_863_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_863_, 0, v_inherited_851_);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22));
v___x_866_ = l_Lake_mkRelPathString(v_dir_852_);
v___x_867_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
v___x_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_865_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = lean_box(0);
v___x_870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_864_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_861_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_858_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = l_Lean_Json_mkObj(v___x_873_);
lean_dec_ref_known(v___x_873_, 2);
v___x_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_853_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v___x_869_);
v___x_877_ = l_Lean_Json_mkObj(v___x_876_);
lean_dec_ref_known(v___x_876_, 2);
return v___x_877_;
}
else
{
lean_object* v_name_878_; lean_object* v_opts_879_; uint8_t v_inherited_880_; lean_object* v_url_881_; lean_object* v_rev_882_; lean_object* v_inputRev_x3f_883_; lean_object* v_subDir_x3f_884_; lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_name_878_ = lean_ctor_get(v_x_848_, 0);
lean_inc(v_name_878_);
v_opts_879_ = lean_ctor_get(v_x_848_, 1);
lean_inc(v_opts_879_);
v_inherited_880_ = lean_ctor_get_uint8(v_x_848_, sizeof(void*)*6);
v_url_881_ = lean_ctor_get(v_x_848_, 2);
lean_inc_ref(v_url_881_);
v_rev_882_ = lean_ctor_get(v_x_848_, 3);
lean_inc_ref(v_rev_882_);
v_inputRev_x3f_883_ = lean_ctor_get(v_x_848_, 4);
lean_inc(v_inputRev_x3f_883_);
v_subDir_x3f_884_ = lean_ctor_get(v_x_848_, 5);
lean_inc(v_subDir_x3f_884_);
lean_dec_ref_known(v_x_848_, 6);
v___x_885_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3));
v___x_886_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_887_ = 1;
v___x_888_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_878_, v___x_887_);
v___x_889_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_886_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__8));
v___x_892_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0(v_opts_879_);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10));
v___x_895_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_895_, 0, v_inherited_880_);
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12));
v___x_898_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_898_, 0, v_url_881_);
v___x_899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14));
v___x_901_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_901_, 0, v_rev_882_);
v___x_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__16));
v___x_904_ = l_Lean_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__1(v_inputRev_x3f_883_);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__18));
v___x_907_ = l_Lean_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_subDir_x3f_884_);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = lean_box(0);
v___x_910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_905_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_902_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_899_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_896_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_893_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_890_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = l_Lean_Json_mkObj(v___x_916_);
lean_dec_ref_known(v___x_916_, 2);
v___x_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_885_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
lean_ctor_set(v___x_919_, 1, v___x_909_);
v___x_920_ = l_Lean_Json_mkObj(v___x_919_);
lean_dec_ref_known(v___x_919_, 2);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_921_, lean_object* v_msg_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v_msg_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0(lean_object* v_00_u03b2_924_, lean_object* v_k_925_, lean_object* v_v_926_, lean_object* v_t_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(v_k_925_, v_v_926_, v_t_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1(lean_object* v_init_929_, lean_object* v_t_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1_spec__5(v_init_929_, v_t_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorIdx___impl(lean_object* v_x_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = lean_obj_tag_nat(v_x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorIdx___impl___boxed(lean_object* v_x_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lake_PackageEntrySrc_ctorIdx___impl(v_x_943_);
lean_dec_ref(v_x_943_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntrySrc_ctorElim___redArg(lean_object* v_t_945_, lean_object* v_k_946_){
_start:
{
if (lean_obj_tag(v_t_945_) == 0)
{
lean_object* v_dir_947_; uint8_t v_copy_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_dir_947_ = lean_ctor_get(v_t_945_, 0);
lean_inc_ref(v_dir_947_);
v_copy_948_ = lean_ctor_get_uint8(v_t_945_, sizeof(void*)*1);
lean_dec_ref_known(v_t_945_, 1);
v___x_949_ = lean_box(v_copy_948_);
v___x_950_ = lean_apply_2(v_k_946_, v_dir_947_, v___x_949_);
return v___x_950_;
}
else
{
lean_object* v_url_951_; lean_object* v_rev_952_; lean_object* v_inputRev_x3f_953_; lean_object* v_subDir_x3f_954_; lean_object* v___x_955_; 
v_url_951_ = lean_ctor_get(v_t_945_, 0);
lean_inc_ref(v_url_951_);
v_rev_952_ = lean_ctor_get(v_t_945_, 1);
lean_inc_ref(v_rev_952_);
v_inputRev_x3f_953_ = lean_ctor_get(v_t_945_, 2);
lean_inc(v_inputRev_x3f_953_);
v_subDir_x3f_954_ = lean_ctor_get(v_t_945_, 3);
lean_inc(v_subDir_x3f_954_);
lean_dec_ref_known(v_t_945_, 4);
v___x_955_ = lean_apply_4(v_k_946_, v_url_951_, v_rev_952_, v_inputRev_x3f_953_, v_subDir_x3f_954_);
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
LEAN_EXPORT lean_object* l_Lake_PackageEntry_toJson(lean_object* v_entry_1015_){
_start:
{
lean_object* v_name_1016_; lean_object* v_scope_1017_; uint8_t v_inherited_1018_; lean_object* v_configFile_1019_; lean_object* v_manifestFile_x3f_1020_; lean_object* v_src_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v_fields_1045_; 
v_name_1016_ = lean_ctor_get(v_entry_1015_, 0);
lean_inc(v_name_1016_);
v_scope_1017_ = lean_ctor_get(v_entry_1015_, 1);
lean_inc_ref(v_scope_1017_);
v_inherited_1018_ = lean_ctor_get_uint8(v_entry_1015_, sizeof(void*)*5);
v_configFile_1019_ = lean_ctor_get(v_entry_1015_, 2);
lean_inc_ref(v_configFile_1019_);
v_manifestFile_x3f_1020_ = lean_ctor_get(v_entry_1015_, 3);
lean_inc(v_manifestFile_x3f_1020_);
v_src_1021_ = lean_ctor_get(v_entry_1015_, 4);
lean_inc_ref(v_src_1021_);
lean_dec_ref(v_entry_1015_);
v___x_1022_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_1023_ = 1;
v___x_1024_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1016_, v___x_1023_);
v___x_1025_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1022_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__0));
v___x_1028_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1028_, 0, v_scope_1017_);
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1027_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__1));
v___x_1031_ = l_Lake_mkRelPathString(v_configFile_1019_);
v___x_1032_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1030_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__2));
v___x_1035_ = l_Lean_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_manifestFile_x3f_1020_);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10));
v___x_1038_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1038_, 0, v_inherited_1018_);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = lean_box(0);
v___x_1041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1039_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1036_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1033_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1029_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v_fields_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_fields_1045_, 0, v___x_1026_);
lean_ctor_set(v_fields_1045_, 1, v___x_1044_);
if (lean_obj_tag(v_src_1021_) == 0)
{
lean_object* v_dir_1046_; uint8_t v_copy_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v_dir_1046_ = lean_ctor_get(v_src_1021_, 0);
lean_inc_ref(v_dir_1046_);
v_copy_1047_ = lean_ctor_get_uint8(v_src_1021_, sizeof(void*)*1);
lean_dec_ref_known(v_src_1021_, 1);
v___x_1048_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__5));
v___x_1049_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22));
v___x_1050_ = l_Lake_mkRelPathString(v_dir_1046_);
v___x_1051_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1049_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__6));
v___x_1054_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1054_, 0, v_copy_1047_);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
lean_ctor_set(v___x_1056_, 1, v___x_1040_);
v___x_1057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1052_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = l_List_appendTR___redArg(v_fields_1045_, v___x_1057_);
v___x_1059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1048_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = l_Lean_Json_mkObj(v___x_1059_);
lean_dec_ref_known(v___x_1059_, 2);
return v___x_1060_;
}
else
{
lean_object* v_url_1061_; lean_object* v_rev_1062_; lean_object* v_inputRev_x3f_1063_; lean_object* v_subDir_x3f_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v_url_1061_ = lean_ctor_get(v_src_1021_, 0);
lean_inc_ref(v_url_1061_);
v_rev_1062_ = lean_ctor_get(v_src_1021_, 1);
lean_inc_ref(v_rev_1062_);
v_inputRev_x3f_1063_ = lean_ctor_get(v_src_1021_, 2);
lean_inc(v_inputRev_x3f_1063_);
v_subDir_x3f_1064_ = lean_ctor_get(v_src_1021_, 3);
lean_inc(v_subDir_x3f_1064_);
lean_dec_ref_known(v_src_1021_, 4);
v___x_1065_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__8));
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
v___x_1072_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__9));
v___x_1073_ = l_Lean_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__1(v_inputRev_x3f_1063_);
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__10));
v___x_1076_ = l_Lean_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_subDir_x3f_1064_);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v___x_1040_);
v___x_1079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1074_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1071_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1068_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = l_List_appendTR___redArg(v_fields_1045_, v___x_1081_);
v___x_1083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1065_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = l_Lean_Json_mkObj(v___x_1083_);
lean_dec_ref_known(v___x_1083_, 2);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_PackageEntry_fromJson_x3f_spec__0(lean_object* v_x_1089_){
_start:
{
if (lean_obj_tag(v_x_1089_) == 0)
{
lean_object* v___x_1090_; 
v___x_1090_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_PackageEntry_fromJson_x3f_spec__0___closed__0));
return v___x_1090_;
}
else
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_Json_getBool_x3f(v_x_1089_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1108_; 
v_a_1100_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1102_ = v___x_1091_;
v_isShared_1103_ = v_isSharedCheck_1108_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1091_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1108_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_a_1100_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v___x_1104_);
v___x_1106_ = v___x_1102_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_PackageEntry_fromJson_x3f_spec__0___boxed(lean_object* v_x_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_Option_fromJson_x3f___at___00Lake_PackageEntry_fromJson_x3f_spec__0(v_x_1109_);
lean_dec(v_x_1109_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0(lean_object* v_x_1112_){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0));
v___x_1114_ = lean_string_append(v___x_1113_, v_x_1112_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0___boxed(lean_object* v_x_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_x_1115_);
lean_dec_ref(v_x_1115_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f(lean_object* v_json_1138_){
_start:
{
lean_object* v_a_1140_; lean_object* v___x_1143_; 
v___x_1143_ = l_Lean_Json_getObj_x3f(v_json_1138_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1152_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1146_ = v___x_1143_;
v_isShared_1147_ = v_isSharedCheck_1152_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1143_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1152_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1148_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_a_1144_);
lean_dec(v_a_1144_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1148_);
v___x_1150_ = v___x_1146_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
else
{
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
v_a_1153_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1143_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1143_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
lean_ctor_set_tag(v___x_1155_, 0);
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1402_; 
v_a_1161_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1163_ = v___x_1143_;
v_isShared_1164_ = v_isSharedCheck_1402_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1143_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1402_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_1166_ = l_Lake_JsonObject_getJson_x3f(v_a_1161_, v___x_1165_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v___x_1167_; 
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v___x_1167_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__0));
v_a_1140_ = v___x_1167_;
goto v___jp_1139_;
}
else
{
lean_object* v_val_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1401_; 
v_val_1168_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1170_ = v___x_1166_;
v_isShared_1171_ = v_isSharedCheck_1401_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_val_1168_);
lean_dec(v___x_1166_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1401_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_Name_fromJson_x3f(v_val_1168_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v___x_1172_, 1);
v___x_1174_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__1));
v___x_1175_ = lean_string_append(v___x_1174_, v_a_1173_);
lean_dec(v_a_1173_);
v_a_1140_ = v___x_1175_;
goto v___jp_1139_;
}
else
{
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1176_; 
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v_a_1176_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1176_);
lean_dec_ref_known(v___x_1172_, 1);
v_a_1140_ = v_a_1176_;
goto v___jp_1139_;
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1400_; 
v_a_1177_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1179_ = v___x_1172_;
v_isShared_1180_ = v_isSharedCheck_1400_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1172_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1400_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v_a_1182_; lean_object* v___y_1194_; uint8_t v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v_a_1198_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; uint8_t v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v_a_1214_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; uint8_t v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v_a_1223_; lean_object* v___y_1235_; lean_object* v___y_1236_; uint8_t v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; uint8_t v_a_1240_; lean_object* v___y_1243_; uint8_t v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1250_; uint8_t v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v_a_1254_; lean_object* v___y_1314_; uint8_t v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1320_; uint8_t v___y_1321_; lean_object* v___y_1322_; lean_object* v_a_1323_; lean_object* v___y_1335_; uint8_t v___y_1336_; lean_object* v___y_1337_; lean_object* v_a_1340_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__0));
v___x_1377_ = l_Lake_JsonObject_getJson_x3f(v_a_1161_, v___x_1376_);
if (lean_obj_tag(v___x_1377_) == 0)
{
goto v___jp_1374_;
}
else
{
lean_object* v_val_1378_; lean_object* v___x_1379_; 
v_val_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_val_1378_);
lean_dec_ref_known(v___x_1377_, 1);
v___x_1379_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(v_val_1378_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1389_; 
lean_del_object(v___x_1179_);
lean_dec(v_a_1177_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1389_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1389_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1384_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__20));
v___x_1385_ = lean_string_append(v___x_1384_, v_a_1380_);
lean_dec(v_a_1380_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1385_);
v___x_1387_ = v___x_1382_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
else
{
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_del_object(v___x_1179_);
lean_dec(v_a_1177_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v_a_1390_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1379_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1379_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set_tag(v___x_1392_, 0);
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
else
{
lean_object* v_a_1398_; 
v_a_1398_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1398_);
lean_dec_ref_known(v___x_1379_, 1);
if (lean_obj_tag(v_a_1398_) == 0)
{
goto v___jp_1374_;
}
else
{
lean_object* v_val_1399_; 
v_val_1399_ = lean_ctor_get(v_a_1398_, 0);
lean_inc(v_val_1399_);
lean_dec_ref_known(v_a_1398_, 1);
v_a_1340_ = v_val_1399_;
goto v___jp_1339_;
}
}
}
}
v___jp_1181_:
{
lean_object* v___x_1183_; uint8_t v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1183_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__2));
v___x_1184_ = 1;
v___x_1185_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_1177_, v___x_1184_);
v___x_1186_ = lean_string_append(v___x_1183_, v___x_1185_);
lean_dec_ref(v___x_1185_);
v___x_1187_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__3));
v___x_1188_ = lean_string_append(v___x_1186_, v___x_1187_);
v___x_1189_ = lean_string_append(v___x_1188_, v_a_1182_);
lean_dec_ref(v_a_1182_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set_tag(v___x_1179_, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1189_);
v___x_1191_ = v___x_1179_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
v___jp_1193_:
{
lean_object* v___x_1200_; 
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___y_1196_);
v___x_1200_ = v___x_1170_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___y_1196_);
v___x_1200_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1201_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1201_, 0, v_a_1177_);
lean_ctor_set(v___x_1201_, 1, v___y_1194_);
lean_ctor_set(v___x_1201_, 2, v___y_1197_);
lean_ctor_set(v___x_1201_, 3, v___x_1200_);
lean_ctor_set(v___x_1201_, 4, v_a_1198_);
lean_ctor_set_uint8(v___x_1201_, sizeof(void*)*5, v___y_1195_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v___x_1201_);
v___x_1203_ = v___x_1163_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
v___jp_1206_:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1215_, 0, v___y_1207_);
lean_ctor_set(v___x_1215_, 1, v___y_1212_);
lean_ctor_set(v___x_1215_, 2, v___y_1209_);
lean_ctor_set(v___x_1215_, 3, v_a_1214_);
v___y_1194_ = v___y_1208_;
v___y_1195_ = v___y_1211_;
v___y_1196_ = v___y_1210_;
v___y_1197_ = v___y_1213_;
v_a_1198_ = v___x_1215_;
goto v___jp_1193_;
}
v___jp_1216_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__10));
v___x_1225_ = l_Lake_JsonObject_getJson_x3f(v_a_1161_, v___x_1224_);
lean_dec(v_a_1161_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v___x_1226_; 
lean_del_object(v___x_1179_);
v___x_1226_ = lean_box(0);
v___y_1207_ = v___y_1217_;
v___y_1208_ = v___y_1218_;
v___y_1209_ = v_a_1223_;
v___y_1210_ = v___y_1221_;
v___y_1211_ = v___y_1220_;
v___y_1212_ = v___y_1219_;
v___y_1213_ = v___y_1222_;
v_a_1214_ = v___x_1226_;
goto v___jp_1206_;
}
else
{
lean_object* v_val_1227_; lean_object* v___x_1228_; 
v_val_1227_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_val_1227_);
lean_dec_ref_known(v___x_1225_, 1);
v___x_1228_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1227_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_dec(v_a_1223_);
lean_dec_ref(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_a_1229_);
lean_dec_ref_known(v___x_1228_, 1);
v___x_1230_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__4));
v___x_1231_ = lean_string_append(v___x_1230_, v_a_1229_);
lean_dec(v_a_1229_);
v_a_1182_ = v___x_1231_;
goto v___jp_1181_;
}
else
{
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1232_; 
lean_dec(v_a_1223_);
lean_dec_ref(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
v_a_1232_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_a_1232_);
lean_dec_ref_known(v___x_1228_, 1);
v_a_1182_ = v_a_1232_;
goto v___jp_1181_;
}
else
{
lean_object* v_a_1233_; 
lean_del_object(v___x_1179_);
v_a_1233_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1228_, 1);
v___y_1207_ = v___y_1217_;
v___y_1208_ = v___y_1218_;
v___y_1209_ = v_a_1223_;
v___y_1210_ = v___y_1221_;
v___y_1211_ = v___y_1220_;
v___y_1212_ = v___y_1219_;
v___y_1213_ = v___y_1222_;
v_a_1214_ = v_a_1233_;
goto v___jp_1206_;
}
}
}
}
v___jp_1234_:
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1241_, 0, v___y_1238_);
lean_ctor_set_uint8(v___x_1241_, sizeof(void*)*1, v_a_1240_);
v___y_1194_ = v___y_1235_;
v___y_1195_ = v___y_1237_;
v___y_1196_ = v___y_1236_;
v___y_1197_ = v___y_1239_;
v_a_1198_ = v___x_1241_;
goto v___jp_1193_;
}
v___jp_1242_:
{
uint8_t v___x_1248_; 
v___x_1248_ = 0;
v___y_1235_ = v___y_1243_;
v___y_1236_ = v___y_1245_;
v___y_1237_ = v___y_1244_;
v___y_1238_ = v___y_1246_;
v___y_1239_ = v___y_1247_;
v_a_1240_ = v___x_1248_;
goto v___jp_1234_;
}
v___jp_1249_:
{
lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1255_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2));
v___x_1256_ = lean_string_dec_eq(v___y_1252_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; uint8_t v___x_1258_; 
v___x_1257_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3));
v___x_1258_ = lean_string_dec_eq(v___y_1252_, v___x_1257_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
lean_dec_ref(v_a_1254_);
lean_dec_ref(v___y_1253_);
lean_dec_ref(v___y_1250_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v___x_1259_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__5));
v___x_1260_ = lean_string_append(v___x_1259_, v___y_1252_);
lean_dec_ref(v___y_1252_);
v___x_1261_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1262_ = lean_string_append(v___x_1260_, v___x_1261_);
v_a_1182_ = v___x_1262_;
goto v___jp_1181_;
}
else
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_dec_ref(v___y_1252_);
v___x_1263_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12));
v___x_1264_ = l_Lake_JsonObject_getJson_x3f(v_a_1161_, v___x_1263_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v___x_1265_; 
lean_dec_ref(v_a_1254_);
lean_dec_ref(v___y_1253_);
lean_dec_ref(v___y_1250_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v___x_1265_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__6));
v_a_1182_ = v___x_1265_;
goto v___jp_1181_;
}
else
{
lean_object* v_val_1266_; lean_object* v___x_1267_; 
v_val_1266_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_val_1266_);
lean_dec_ref_known(v___x_1264_, 1);
v___x_1267_ = l_Lean_Json_getStr_x3f(v_val_1266_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
lean_dec_ref(v_a_1254_);
lean_dec_ref(v___y_1253_);
lean_dec_ref(v___y_1250_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1267_, 1);
v___x_1269_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__7));
v___x_1270_ = lean_string_append(v___x_1269_, v_a_1268_);
lean_dec(v_a_1268_);
v_a_1182_ = v___x_1270_;
goto v___jp_1181_;
}
else
{
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1271_; 
lean_dec_ref(v_a_1254_);
lean_dec_ref(v___y_1253_);
lean_dec_ref(v___y_1250_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v_a_1271_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1271_);
lean_dec_ref_known(v___x_1267_, 1);
v_a_1182_ = v_a_1271_;
goto v___jp_1181_;
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v_a_1272_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1272_);
lean_dec_ref_known(v___x_1267_, 1);
v___x_1273_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14));
v___x_1274_ = l_Lake_JsonObject_getJson_x3f(v_a_1161_, v___x_1273_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v___x_1275_; 
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1254_);
lean_dec_ref(v___y_1253_);
lean_dec_ref(v___y_1250_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v___x_1275_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__8));
v_a_1182_ = v___x_1275_;
goto v___jp_1181_;
}
else
{
lean_object* v_val_1276_; lean_object* v___x_1277_; 
v_val_1276_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_val_1276_);
lean_dec_ref_known(v___x_1274_, 1);
v___x_1277_ = l_Lean_Json_getStr_x3f(v_val_1276_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1254_);
lean_dec_ref(v___y_1253_);
lean_dec_ref(v___y_1250_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref_known(v___x_1277_, 1);
v___x_1279_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__9));
v___x_1280_ = lean_string_append(v___x_1279_, v_a_1278_);
lean_dec(v_a_1278_);
v_a_1182_ = v___x_1280_;
goto v___jp_1181_;
}
else
{
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1281_; 
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1254_);
lean_dec_ref(v___y_1253_);
lean_dec_ref(v___y_1250_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v_a_1281_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_1277_, 1);
v_a_1182_ = v_a_1281_;
goto v___jp_1181_;
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v_a_1282_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1282_);
lean_dec_ref_known(v___x_1277_, 1);
v___x_1283_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__9));
v___x_1284_ = l_Lake_JsonObject_getJson_x3f(v_a_1161_, v___x_1283_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_box(0);
v___y_1217_ = v_a_1272_;
v___y_1218_ = v___y_1250_;
v___y_1219_ = v_a_1282_;
v___y_1220_ = v___y_1251_;
v___y_1221_ = v_a_1254_;
v___y_1222_ = v___y_1253_;
v_a_1223_ = v___x_1285_;
goto v___jp_1216_;
}
else
{
lean_object* v_val_1286_; lean_object* v___x_1287_; 
v_val_1286_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_val_1286_);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1287_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(v_val_1286_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
lean_dec(v_a_1282_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1254_);
lean_dec_ref(v___y_1253_);
lean_dec_ref(v___y_1250_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1287_, 1);
v___x_1289_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__10));
v___x_1290_ = lean_string_append(v___x_1289_, v_a_1288_);
lean_dec(v_a_1288_);
v_a_1182_ = v___x_1290_;
goto v___jp_1181_;
}
else
{
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1291_; 
lean_dec(v_a_1282_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1254_);
lean_dec_ref(v___y_1253_);
lean_dec_ref(v___y_1250_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v_a_1291_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1291_);
lean_dec_ref_known(v___x_1287_, 1);
v_a_1182_ = v_a_1291_;
goto v___jp_1181_;
}
else
{
lean_object* v_a_1292_; 
v_a_1292_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1292_);
lean_dec_ref_known(v___x_1287_, 1);
v___y_1217_ = v_a_1272_;
v___y_1218_ = v___y_1250_;
v___y_1219_ = v_a_1282_;
v___y_1220_ = v___y_1251_;
v___y_1221_ = v_a_1254_;
v___y_1222_ = v___y_1253_;
v_a_1223_ = v_a_1292_;
goto v___jp_1216_;
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
lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_dec_ref(v___y_1252_);
v___x_1293_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22));
v___x_1294_ = l_Lake_JsonObject_getJson_x3f(v_a_1161_, v___x_1293_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v___x_1295_; 
lean_dec_ref(v_a_1254_);
lean_dec_ref(v___y_1253_);
lean_dec_ref(v___y_1250_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v___x_1295_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__11));
v_a_1182_ = v___x_1295_;
goto v___jp_1181_;
}
else
{
lean_object* v_val_1296_; lean_object* v___x_1297_; 
v_val_1296_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_val_1296_);
lean_dec_ref_known(v___x_1294_, 1);
v___x_1297_ = l_Lean_Json_getStr_x3f(v_val_1296_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_dec_ref(v_a_1254_);
lean_dec_ref(v___y_1253_);
lean_dec_ref(v___y_1250_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
lean_dec_ref_known(v___x_1297_, 1);
v___x_1299_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__12));
v___x_1300_ = lean_string_append(v___x_1299_, v_a_1298_);
lean_dec(v_a_1298_);
v_a_1182_ = v___x_1300_;
goto v___jp_1181_;
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v_a_1301_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1297_, 1);
v___x_1302_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__6));
v___x_1303_ = l_Lake_JsonObject_getJson_x3f(v_a_1161_, v___x_1302_);
lean_dec(v_a_1161_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_del_object(v___x_1179_);
v___y_1243_ = v___y_1250_;
v___y_1244_ = v___y_1251_;
v___y_1245_ = v_a_1254_;
v___y_1246_ = v_a_1301_;
v___y_1247_ = v___y_1253_;
goto v___jp_1242_;
}
else
{
lean_object* v_val_1304_; lean_object* v___x_1305_; 
v_val_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_val_1304_);
lean_dec_ref_known(v___x_1303_, 1);
v___x_1305_ = l_Lean_Option_fromJson_x3f___at___00Lake_PackageEntry_fromJson_x3f_spec__0(v_val_1304_);
lean_dec(v_val_1304_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1254_);
lean_dec_ref(v___y_1253_);
lean_dec_ref(v___y_1250_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1306_);
lean_dec_ref_known(v___x_1305_, 1);
v___x_1307_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__13));
v___x_1308_ = lean_string_append(v___x_1307_, v_a_1306_);
lean_dec(v_a_1306_);
v_a_1182_ = v___x_1308_;
goto v___jp_1181_;
}
else
{
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1309_; 
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1254_);
lean_dec_ref(v___y_1253_);
lean_dec_ref(v___y_1250_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
v_a_1309_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1305_, 1);
v_a_1182_ = v_a_1309_;
goto v___jp_1181_;
}
else
{
lean_object* v_a_1310_; 
lean_del_object(v___x_1179_);
v_a_1310_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1310_);
lean_dec_ref_known(v___x_1305_, 1);
if (lean_obj_tag(v_a_1310_) == 0)
{
v___y_1243_ = v___y_1250_;
v___y_1244_ = v___y_1251_;
v___y_1245_ = v_a_1254_;
v___y_1246_ = v_a_1301_;
v___y_1247_ = v___y_1253_;
goto v___jp_1242_;
}
else
{
lean_object* v_val_1311_; uint8_t v___x_1312_; 
v_val_1311_ = lean_ctor_get(v_a_1310_, 0);
lean_inc(v_val_1311_);
lean_dec_ref_known(v_a_1310_, 1);
v___x_1312_ = lean_unbox(v_val_1311_);
lean_dec(v_val_1311_);
v___y_1235_ = v___y_1250_;
v___y_1236_ = v_a_1254_;
v___y_1237_ = v___y_1251_;
v___y_1238_ = v_a_1301_;
v___y_1239_ = v___y_1253_;
v_a_1240_ = v___x_1312_;
goto v___jp_1234_;
}
}
}
}
}
}
}
}
v___jp_1313_:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Lake_defaultManifestFile;
v___y_1250_ = v___y_1314_;
v___y_1251_ = v___y_1315_;
v___y_1252_ = v___y_1316_;
v___y_1253_ = v___y_1317_;
v_a_1254_ = v___x_1318_;
goto v___jp_1249_;
}
v___jp_1319_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__2));
v___x_1325_ = l_Lake_JsonObject_getJson_x3f(v_a_1161_, v___x_1324_);
if (lean_obj_tag(v___x_1325_) == 0)
{
v___y_1314_ = v___y_1320_;
v___y_1315_ = v___y_1321_;
v___y_1316_ = v___y_1322_;
v___y_1317_ = v_a_1323_;
goto v___jp_1313_;
}
else
{
lean_object* v_val_1326_; lean_object* v___x_1327_; 
v_val_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_val_1326_);
lean_dec_ref_known(v___x_1325_, 1);
v___x_1327_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1326_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_dec_ref(v_a_1323_);
lean_dec_ref(v___y_1322_);
lean_dec_ref(v___y_1320_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1327_, 1);
v___x_1329_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__14));
v___x_1330_ = lean_string_append(v___x_1329_, v_a_1328_);
lean_dec(v_a_1328_);
v_a_1182_ = v___x_1330_;
goto v___jp_1181_;
}
else
{
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1331_; 
lean_dec_ref(v_a_1323_);
lean_dec_ref(v___y_1322_);
lean_dec_ref(v___y_1320_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v_a_1331_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1331_);
lean_dec_ref_known(v___x_1327_, 1);
v_a_1182_ = v_a_1331_;
goto v___jp_1181_;
}
else
{
lean_object* v_a_1332_; 
v_a_1332_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1332_);
lean_dec_ref_known(v___x_1327_, 1);
if (lean_obj_tag(v_a_1332_) == 0)
{
v___y_1314_ = v___y_1320_;
v___y_1315_ = v___y_1321_;
v___y_1316_ = v___y_1322_;
v___y_1317_ = v_a_1323_;
goto v___jp_1313_;
}
else
{
lean_object* v_val_1333_; 
v_val_1333_ = lean_ctor_get(v_a_1332_, 0);
lean_inc(v_val_1333_);
lean_dec_ref_known(v_a_1332_, 1);
v___y_1250_ = v___y_1320_;
v___y_1251_ = v___y_1321_;
v___y_1252_ = v___y_1322_;
v___y_1253_ = v_a_1323_;
v_a_1254_ = v_val_1333_;
goto v___jp_1249_;
}
}
}
}
}
v___jp_1334_:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lake_defaultConfigFile;
v___y_1320_ = v___y_1335_;
v___y_1321_ = v___y_1336_;
v___y_1322_ = v___y_1337_;
v_a_1323_ = v___x_1338_;
goto v___jp_1319_;
}
v___jp_1339_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__3));
v___x_1342_ = l_Lake_JsonObject_getJson_x3f(v_a_1161_, v___x_1341_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v___x_1343_; 
lean_dec_ref(v_a_1340_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v___x_1343_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__15));
v_a_1182_ = v___x_1343_;
goto v___jp_1181_;
}
else
{
lean_object* v_val_1344_; lean_object* v___x_1345_; 
v_val_1344_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_val_1344_);
lean_dec_ref_known(v___x_1342_, 1);
v___x_1345_ = l_Lean_Json_getStr_x3f(v_val_1344_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
lean_dec_ref(v_a_1340_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1345_, 1);
v___x_1347_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__16));
v___x_1348_ = lean_string_append(v___x_1347_, v_a_1346_);
lean_dec(v_a_1346_);
v_a_1182_ = v___x_1348_;
goto v___jp_1181_;
}
else
{
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1349_; 
lean_dec_ref(v_a_1340_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v_a_1349_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1349_);
lean_dec_ref_known(v___x_1345_, 1);
v_a_1182_ = v_a_1349_;
goto v___jp_1181_;
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v_a_1350_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1345_, 1);
v___x_1351_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10));
v___x_1352_ = l_Lake_JsonObject_getJson_x3f(v_a_1161_, v___x_1351_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v___x_1353_; 
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1340_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v___x_1353_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__17));
v_a_1182_ = v___x_1353_;
goto v___jp_1181_;
}
else
{
lean_object* v_val_1354_; lean_object* v___x_1355_; 
v_val_1354_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_val_1354_);
lean_dec_ref_known(v___x_1352_, 1);
v___x_1355_ = l_Lean_Json_getBool_x3f(v_val_1354_);
lean_dec(v_val_1354_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1340_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v___x_1355_, 1);
v___x_1357_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__18));
v___x_1358_ = lean_string_append(v___x_1357_, v_a_1356_);
lean_dec(v_a_1356_);
v_a_1182_ = v___x_1358_;
goto v___jp_1181_;
}
else
{
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1359_; 
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1340_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v_a_1359_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1359_);
lean_dec_ref_known(v___x_1355_, 1);
v_a_1182_ = v_a_1359_;
goto v___jp_1181_;
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v_a_1360_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1360_);
lean_dec_ref_known(v___x_1355_, 1);
v___x_1361_ = ((lean_object*)(l_Lake_PackageEntry_toJson___closed__1));
v___x_1362_ = l_Lake_JsonObject_getJson_x3f(v_a_1161_, v___x_1361_);
if (lean_obj_tag(v___x_1362_) == 0)
{
uint8_t v___x_1363_; 
v___x_1363_ = lean_unbox(v_a_1360_);
lean_dec(v_a_1360_);
v___y_1335_ = v_a_1340_;
v___y_1336_ = v___x_1363_;
v___y_1337_ = v_a_1350_;
goto v___jp_1334_;
}
else
{
lean_object* v_val_1364_; lean_object* v___x_1365_; 
v_val_1364_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_val_1364_);
lean_dec_ref_known(v___x_1362_, 1);
v___x_1365_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1364_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_dec(v_a_1360_);
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1340_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref_known(v___x_1365_, 1);
v___x_1367_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__19));
v___x_1368_ = lean_string_append(v___x_1367_, v_a_1366_);
lean_dec(v_a_1366_);
v_a_1182_ = v___x_1368_;
goto v___jp_1181_;
}
else
{
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1369_; 
lean_dec(v_a_1360_);
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1340_);
lean_del_object(v___x_1170_);
lean_del_object(v___x_1163_);
lean_dec(v_a_1161_);
v_a_1369_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1365_, 1);
v_a_1182_ = v_a_1369_;
goto v___jp_1181_;
}
else
{
lean_object* v_a_1370_; 
v_a_1370_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1365_, 1);
if (lean_obj_tag(v_a_1370_) == 0)
{
uint8_t v___x_1371_; 
v___x_1371_ = lean_unbox(v_a_1360_);
lean_dec(v_a_1360_);
v___y_1335_ = v_a_1340_;
v___y_1336_ = v___x_1371_;
v___y_1337_ = v_a_1350_;
goto v___jp_1334_;
}
else
{
lean_object* v_val_1372_; uint8_t v___x_1373_; 
v_val_1372_ = lean_ctor_get(v_a_1370_, 0);
lean_inc(v_val_1372_);
lean_dec_ref_known(v_a_1370_, 1);
v___x_1373_ = lean_unbox(v_a_1360_);
lean_dec(v_a_1360_);
v___y_1320_ = v_a_1340_;
v___y_1321_ = v___x_1373_;
v___y_1322_ = v_a_1350_;
v_a_1323_ = v_val_1372_;
goto v___jp_1319_;
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
v___jp_1374_:
{
lean_object* v___x_1375_; 
v___x_1375_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v_a_1340_ = v___x_1375_;
goto v___jp_1339_;
}
}
}
}
}
}
}
}
}
v___jp_1139_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_a_1140_);
lean_dec_ref(v_a_1140_);
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
return v___x_1142_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_prettyName(lean_object* v_entry_1405_){
_start:
{
lean_object* v_name_1406_; uint8_t v___x_1407_; lean_object* v___x_1408_; 
v_name_1406_ = lean_ctor_get(v_entry_1405_, 0);
lean_inc(v_name_1406_);
lean_dec_ref(v_entry_1405_);
v___x_1407_ = 0;
v___x_1408_ = l_Lean_Name_toString(v_name_1406_, v___x_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_dirName(lean_object* v_entry_1409_){
_start:
{
lean_object* v_name_1410_; uint8_t v___x_1411_; lean_object* v___x_1412_; 
v_name_1410_ = lean_ctor_get(v_entry_1409_, 0);
lean_inc(v_name_1410_);
lean_dec_ref(v_entry_1409_);
v___x_1411_ = 0;
v___x_1412_ = l_Lean_Name_toString(v_name_1410_, v___x_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_inputRev_x3f(lean_object* v_entry_1413_){
_start:
{
lean_object* v_src_1414_; 
v_src_1414_ = lean_ctor_get(v_entry_1413_, 4);
if (lean_obj_tag(v_src_1414_) == 0)
{
lean_object* v___x_1415_; 
v___x_1415_ = lean_box(0);
return v___x_1415_;
}
else
{
lean_object* v_inputRev_x3f_1416_; 
v_inputRev_x3f_1416_ = lean_ctor_get(v_src_1414_, 2);
lean_inc(v_inputRev_x3f_1416_);
return v_inputRev_x3f_1416_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_inputRev_x3f___boxed(lean_object* v_entry_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lake_PackageEntry_inputRev_x3f(v_entry_1417_);
lean_dec_ref(v_entry_1417_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setInherited(lean_object* v_entry_1419_){
_start:
{
lean_object* v_name_1420_; lean_object* v_scope_1421_; lean_object* v_configFile_1422_; lean_object* v_manifestFile_x3f_1423_; lean_object* v_src_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1432_; 
v_name_1420_ = lean_ctor_get(v_entry_1419_, 0);
v_scope_1421_ = lean_ctor_get(v_entry_1419_, 1);
v_configFile_1422_ = lean_ctor_get(v_entry_1419_, 2);
v_manifestFile_x3f_1423_ = lean_ctor_get(v_entry_1419_, 3);
v_src_1424_ = lean_ctor_get(v_entry_1419_, 4);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_entry_1419_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1426_ = v_entry_1419_;
v_isShared_1427_ = v_isSharedCheck_1432_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_src_1424_);
lean_inc(v_manifestFile_x3f_1423_);
lean_inc(v_configFile_1422_);
lean_inc(v_scope_1421_);
lean_inc(v_name_1420_);
lean_dec(v_entry_1419_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1432_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
uint8_t v___x_1428_; lean_object* v___x_1430_; 
v___x_1428_ = 1;
if (v_isShared_1427_ == 0)
{
v___x_1430_ = v___x_1426_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_name_1420_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_scope_1421_);
lean_ctor_set(v_reuseFailAlloc_1431_, 2, v_configFile_1422_);
lean_ctor_set(v_reuseFailAlloc_1431_, 3, v_manifestFile_x3f_1423_);
lean_ctor_set(v_reuseFailAlloc_1431_, 4, v_src_1424_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*5, v___x_1428_);
return v___x_1430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setConfigFile(lean_object* v_path_1433_, lean_object* v_entry_1434_){
_start:
{
lean_object* v_name_1435_; lean_object* v_scope_1436_; uint8_t v_inherited_1437_; lean_object* v_manifestFile_x3f_1438_; lean_object* v_src_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
v_name_1435_ = lean_ctor_get(v_entry_1434_, 0);
v_scope_1436_ = lean_ctor_get(v_entry_1434_, 1);
v_inherited_1437_ = lean_ctor_get_uint8(v_entry_1434_, sizeof(void*)*5);
v_manifestFile_x3f_1438_ = lean_ctor_get(v_entry_1434_, 3);
v_src_1439_ = lean_ctor_get(v_entry_1434_, 4);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_entry_1434_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; 
v_unused_1447_ = lean_ctor_get(v_entry_1434_, 2);
lean_dec(v_unused_1447_);
v___x_1441_ = v_entry_1434_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_src_1439_);
lean_inc(v_manifestFile_x3f_1438_);
lean_inc(v_scope_1436_);
lean_inc(v_name_1435_);
lean_dec(v_entry_1434_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 2, v_path_1433_);
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_name_1435_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_scope_1436_);
lean_ctor_set(v_reuseFailAlloc_1445_, 2, v_path_1433_);
lean_ctor_set(v_reuseFailAlloc_1445_, 3, v_manifestFile_x3f_1438_);
lean_ctor_set(v_reuseFailAlloc_1445_, 4, v_src_1439_);
lean_ctor_set_uint8(v_reuseFailAlloc_1445_, sizeof(void*)*5, v_inherited_1437_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setManifestFile(lean_object* v_path_x3f_1448_, lean_object* v_entry_1449_){
_start:
{
lean_object* v_name_1450_; lean_object* v_scope_1451_; uint8_t v_inherited_1452_; lean_object* v_configFile_1453_; lean_object* v_src_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
v_name_1450_ = lean_ctor_get(v_entry_1449_, 0);
v_scope_1451_ = lean_ctor_get(v_entry_1449_, 1);
v_inherited_1452_ = lean_ctor_get_uint8(v_entry_1449_, sizeof(void*)*5);
v_configFile_1453_ = lean_ctor_get(v_entry_1449_, 2);
v_src_1454_ = lean_ctor_get(v_entry_1449_, 4);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_entry_1449_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v_entry_1449_, 3);
lean_dec(v_unused_1462_);
v___x_1456_ = v_entry_1449_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_src_1454_);
lean_inc(v_configFile_1453_);
lean_inc(v_scope_1451_);
lean_inc(v_name_1450_);
lean_dec(v_entry_1449_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 3, v_path_x3f_1448_);
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_name_1450_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_scope_1451_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v_configFile_1453_);
lean_ctor_set(v_reuseFailAlloc_1460_, 3, v_path_x3f_1448_);
lean_ctor_set(v_reuseFailAlloc_1460_, 4, v_src_1454_);
lean_ctor_set_uint8(v_reuseFailAlloc_1460_, sizeof(void*)*5, v_inherited_1452_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_inDirectory(lean_object* v_pkgDir_1463_, lean_object* v_entry_1464_){
_start:
{
lean_object* v_src_1465_; 
v_src_1465_ = lean_ctor_get(v_entry_1464_, 4);
lean_inc_ref(v_src_1465_);
if (lean_obj_tag(v_src_1465_) == 0)
{
uint8_t v_copy_1466_; 
v_copy_1466_ = lean_ctor_get_uint8(v_src_1465_, sizeof(void*)*1);
if (v_copy_1466_ == 0)
{
lean_object* v_name_1467_; lean_object* v_scope_1468_; uint8_t v_inherited_1469_; lean_object* v_configFile_1470_; lean_object* v_manifestFile_x3f_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1487_; 
v_name_1467_ = lean_ctor_get(v_entry_1464_, 0);
v_scope_1468_ = lean_ctor_get(v_entry_1464_, 1);
v_inherited_1469_ = lean_ctor_get_uint8(v_entry_1464_, sizeof(void*)*5);
v_configFile_1470_ = lean_ctor_get(v_entry_1464_, 2);
v_manifestFile_x3f_1471_ = lean_ctor_get(v_entry_1464_, 3);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_entry_1464_);
if (v_isSharedCheck_1487_ == 0)
{
lean_object* v_unused_1488_; 
v_unused_1488_ = lean_ctor_get(v_entry_1464_, 4);
lean_dec(v_unused_1488_);
v___x_1473_ = v_entry_1464_;
v_isShared_1474_ = v_isSharedCheck_1487_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_manifestFile_x3f_1471_);
lean_inc(v_configFile_1470_);
lean_inc(v_scope_1468_);
lean_inc(v_name_1467_);
lean_dec(v_entry_1464_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1487_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v_dir_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1486_; 
v_dir_1475_ = lean_ctor_get(v_src_1465_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_src_1465_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1477_ = v_src_1465_;
v_isShared_1478_ = v_isSharedCheck_1486_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_dir_1475_);
lean_dec(v_src_1465_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1486_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; lean_object* v___x_1481_; 
v___x_1479_ = l_Lake_joinRelative(v_pkgDir_1463_, v_dir_1475_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1479_);
v___x_1481_ = v___x_1477_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1479_);
lean_ctor_set_uint8(v_reuseFailAlloc_1485_, sizeof(void*)*1, v_copy_1466_);
v___x_1481_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1483_; 
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 4, v___x_1481_);
v___x_1483_ = v___x_1473_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_name_1467_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_scope_1468_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_configFile_1470_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v_manifestFile_x3f_1471_);
lean_ctor_set(v_reuseFailAlloc_1484_, 4, v___x_1481_);
lean_ctor_set_uint8(v_reuseFailAlloc_1484_, sizeof(void*)*5, v_inherited_1469_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_src_1465_, 1);
lean_dec_ref(v_pkgDir_1463_);
return v_entry_1464_;
}
}
else
{
lean_dec_ref(v_src_1465_);
lean_dec_ref(v_pkgDir_1463_);
return v_entry_1464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(lean_object* v_x_1489_){
_start:
{
if (lean_obj_tag(v_x_1489_) == 0)
{
lean_object* v_name_1490_; uint8_t v_inherited_1491_; lean_object* v_dir_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v_name_1490_ = lean_ctor_get(v_x_1489_, 0);
v_inherited_1491_ = lean_ctor_get_uint8(v_x_1489_, sizeof(void*)*3);
v_dir_1492_ = lean_ctor_get(v_x_1489_, 2);
v___x_1493_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_1494_ = l_Lake_defaultConfigFile;
v___x_1495_ = lean_box(0);
v___x_1496_ = 0;
lean_inc_ref(v_dir_1492_);
v___x_1497_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1497_, 0, v_dir_1492_);
lean_ctor_set_uint8(v___x_1497_, sizeof(void*)*1, v___x_1496_);
lean_inc(v_name_1490_);
v___x_1498_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1498_, 0, v_name_1490_);
lean_ctor_set(v___x_1498_, 1, v___x_1493_);
lean_ctor_set(v___x_1498_, 2, v___x_1494_);
lean_ctor_set(v___x_1498_, 3, v___x_1495_);
lean_ctor_set(v___x_1498_, 4, v___x_1497_);
lean_ctor_set_uint8(v___x_1498_, sizeof(void*)*5, v_inherited_1491_);
return v___x_1498_;
}
else
{
lean_object* v_name_1499_; uint8_t v_inherited_1500_; lean_object* v_url_1501_; lean_object* v_rev_1502_; lean_object* v_inputRev_x3f_1503_; lean_object* v_subDir_x3f_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v_name_1499_ = lean_ctor_get(v_x_1489_, 0);
v_inherited_1500_ = lean_ctor_get_uint8(v_x_1489_, sizeof(void*)*6);
v_url_1501_ = lean_ctor_get(v_x_1489_, 2);
v_rev_1502_ = lean_ctor_get(v_x_1489_, 3);
v_inputRev_x3f_1503_ = lean_ctor_get(v_x_1489_, 4);
v_subDir_x3f_1504_ = lean_ctor_get(v_x_1489_, 5);
v___x_1505_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_1506_ = l_Lake_defaultConfigFile;
v___x_1507_ = lean_box(0);
lean_inc(v_subDir_x3f_1504_);
lean_inc(v_inputRev_x3f_1503_);
lean_inc_ref(v_rev_1502_);
lean_inc_ref(v_url_1501_);
v___x_1508_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1508_, 0, v_url_1501_);
lean_ctor_set(v___x_1508_, 1, v_rev_1502_);
lean_ctor_set(v___x_1508_, 2, v_inputRev_x3f_1503_);
lean_ctor_set(v___x_1508_, 3, v_subDir_x3f_1504_);
lean_inc(v_name_1499_);
v___x_1509_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1509_, 0, v_name_1499_);
lean_ctor_set(v___x_1509_, 1, v___x_1505_);
lean_ctor_set(v___x_1509_, 2, v___x_1506_);
lean_ctor_set(v___x_1509_, 3, v___x_1507_);
lean_ctor_set(v___x_1509_, 4, v___x_1508_);
lean_ctor_set_uint8(v___x_1509_, sizeof(void*)*5, v_inherited_1500_);
return v___x_1509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6___boxed(lean_object* v_x_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(v_x_1510_);
lean_dec_ref(v_x_1510_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_addPackage(lean_object* v_entry_1512_, lean_object* v_self_1513_){
_start:
{
lean_object* v_name_1514_; lean_object* v_lakeDir_1515_; uint8_t v_fixedToolchain_1516_; lean_object* v_packagesDir_x3f_1517_; lean_object* v_packages_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1526_; 
v_name_1514_ = lean_ctor_get(v_self_1513_, 0);
v_lakeDir_1515_ = lean_ctor_get(v_self_1513_, 1);
v_fixedToolchain_1516_ = lean_ctor_get_uint8(v_self_1513_, sizeof(void*)*4);
v_packagesDir_x3f_1517_ = lean_ctor_get(v_self_1513_, 2);
v_packages_1518_ = lean_ctor_get(v_self_1513_, 3);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_self_1513_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1520_ = v_self_1513_;
v_isShared_1521_ = v_isSharedCheck_1526_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_packages_1518_);
lean_inc(v_packagesDir_x3f_1517_);
lean_inc(v_lakeDir_1515_);
lean_inc(v_name_1514_);
lean_dec(v_self_1513_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1526_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; lean_object* v___x_1524_; 
v___x_1522_ = lean_array_push(v_packages_1518_, v_entry_1512_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 3, v___x_1522_);
v___x_1524_ = v___x_1520_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_name_1514_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_lakeDir_1515_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_packagesDir_x3f_1517_);
lean_ctor_set(v_reuseFailAlloc_1525_, 3, v___x_1522_);
lean_ctor_set_uint8(v_reuseFailAlloc_1525_, sizeof(void*)*4, v_fixedToolchain_1516_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(size_t v_sz_1527_, size_t v_i_1528_, lean_object* v_bs_1529_){
_start:
{
uint8_t v___x_1530_; 
v___x_1530_ = lean_usize_dec_lt(v_i_1528_, v_sz_1527_);
if (v___x_1530_ == 0)
{
return v_bs_1529_;
}
else
{
lean_object* v_v_1531_; lean_object* v___x_1532_; lean_object* v_bs_x27_1533_; lean_object* v___x_1534_; size_t v___x_1535_; size_t v___x_1536_; lean_object* v___x_1537_; 
v_v_1531_ = lean_array_uget(v_bs_1529_, v_i_1528_);
v___x_1532_ = lean_unsigned_to_nat(0u);
v_bs_x27_1533_ = lean_array_uset(v_bs_1529_, v_i_1528_, v___x_1532_);
v___x_1534_ = l_Lake_PackageEntry_toJson(v_v_1531_);
v___x_1535_ = ((size_t)1ULL);
v___x_1536_ = lean_usize_add(v_i_1528_, v___x_1535_);
v___x_1537_ = lean_array_uset(v_bs_x27_1533_, v_i_1528_, v___x_1534_);
v_i_1528_ = v___x_1536_;
v_bs_1529_ = v___x_1537_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1527_ = stack[0].m_num;
size_t v_i_1528_ = stack[1].m_num;
lean_object* v_bs_1529_ = stack[2].m_obj;
lean_object* v_res_1539_;
v_res_1539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(v_sz_1527_, v_i_1528_, v_bs_1529_);
stack->m_obj
 = v_res_1539_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1540_, lean_object* v_i_1541_, lean_object* v_bs_1542_){
_start:
{
size_t v_sz_boxed_1543_; size_t v_i_boxed_1544_; lean_object* v_res_1545_; 
v_sz_boxed_1543_ = lean_unbox_usize(v_sz_1540_);
lean_dec(v_sz_1540_);
v_i_boxed_1544_ = lean_unbox_usize(v_i_1541_);
lean_dec(v_i_1541_);
v_res_1545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(v_sz_boxed_1543_, v_i_boxed_1544_, v_bs_1542_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_Manifest_toJson_spec__0(lean_object* v_a_1546_){
_start:
{
size_t v_sz_1547_; size_t v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v_sz_1547_ = lean_array_size(v_a_1546_);
v___x_1548_ = ((size_t)0ULL);
v___x_1549_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(v_sz_1547_, v___x_1548_, v_a_1546_);
v___x_1550_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
return v___x_1550_;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__1(void){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = ((lean_object*)(l_Lake_Manifest_version___closed__2));
v___x_1553_ = l_Lake_StdVer_toString(v___x_1552_);
return v___x_1553_;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__2(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__1, &l_Lake_Manifest_toJson___closed__1_once, _init_l_Lake_Manifest_toJson___closed__1);
v___x_1555_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
return v___x_1555_;
}
}
static lean_object* _init_l_Lake_Manifest_toJson___closed__3(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__2, &l_Lake_Manifest_toJson___closed__2_once, _init_l_Lake_Manifest_toJson___closed__2);
v___x_1557_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__0));
v___x_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
lean_ctor_set(v___x_1558_, 1, v___x_1556_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_toJson(lean_object* v_self_1563_){
_start:
{
lean_object* v_name_1564_; lean_object* v_lakeDir_1565_; uint8_t v_fixedToolchain_1566_; lean_object* v_packagesDir_x3f_1567_; lean_object* v_packages_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v_name_1564_ = lean_ctor_get(v_self_1563_, 0);
lean_inc(v_name_1564_);
v_lakeDir_1565_ = lean_ctor_get(v_self_1563_, 1);
lean_inc_ref(v_lakeDir_1565_);
v_fixedToolchain_1566_ = lean_ctor_get_uint8(v_self_1563_, sizeof(void*)*4);
v_packagesDir_x3f_1567_ = lean_ctor_get(v_self_1563_, 2);
lean_inc(v_packagesDir_x3f_1567_);
v_packages_1568_ = lean_ctor_get(v_self_1563_, 3);
lean_inc_ref(v_packages_1568_);
lean_dec_ref(v_self_1563_);
v___x_1569_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__3, &l_Lake_Manifest_toJson___closed__3_once, _init_l_Lake_Manifest_toJson___closed__3);
v___x_1570_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__4));
v___x_1571_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1571_, 0, v_fixedToolchain_1566_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1570_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_1574_ = 1;
v___x_1575_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1564_, v___x_1574_);
v___x_1576_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
v___x_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1573_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__5));
v___x_1579_ = l_Lake_mkRelPathString(v_lakeDir_1565_);
v___x_1580_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
v___x_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1578_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__6));
v___x_1583_ = l_Lean_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_packagesDir_x3f_1567_);
v___x_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1582_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
v___x_1585_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__7));
v___x_1586_ = l_Lean_Array_toJson___at___00Lake_Manifest_toJson_spec__0(v_packages_1568_);
v___x_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1585_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = lean_box(0);
v___x_1589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1584_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1581_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1577_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1572_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1569_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = l_Lean_Json_mkObj(v___x_1594_);
lean_dec_ref_known(v___x_1594_, 2);
return v___x_1595_;
}
}
static lean_object* _init_l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6(void){
_start:
{
lean_object* v_natZero_1606_; lean_object* v_intZero_1607_; 
v_natZero_1606_ = lean_unsigned_to_nat(0u);
v_intZero_1607_ = lean_nat_to_int(v_natZero_1606_);
return v_intZero_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(lean_object* v_obj_1612_){
_start:
{
lean_object* v_ver_1614_; lean_object* v___y_1623_; lean_object* v_ver_1631_; lean_object* v_major_1632_; lean_object* v_a_1649_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__0));
v___x_1673_ = l_Lake_JsonObject_getJson_x3f(v_obj_1612_, v___x_1672_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7));
v___x_1675_ = l_Lake_JsonObject_getJson_x3f(v_obj_1612_, v___x_1674_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v___x_1676_; 
v___x_1676_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__9));
return v___x_1676_;
}
else
{
lean_object* v_val_1677_; 
v_val_1677_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_val_1677_);
lean_dec_ref_known(v___x_1675_, 1);
v_a_1649_ = v_val_1677_;
goto v___jp_1648_;
}
}
else
{
lean_object* v_val_1678_; 
v_val_1678_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_val_1678_);
lean_dec_ref_known(v___x_1673_, 1);
v_a_1649_ = v_val_1678_;
goto v___jp_1648_;
}
v___jp_1613_:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1615_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__0));
v___x_1616_ = lean_unsigned_to_nat(80u);
v___x_1617_ = l_Lean_Json_pretty(v_ver_1614_, v___x_1616_);
v___x_1618_ = lean_string_append(v___x_1615_, v___x_1617_);
lean_dec_ref(v___x_1617_);
v___x_1619_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__1));
v___x_1620_ = lean_string_append(v___x_1618_, v___x_1619_);
v___x_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
return v___x_1621_;
}
v___jp_1622_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1624_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__2));
v___x_1625_ = l_Lake_SemVerCore_toString(v___y_1623_);
v___x_1626_ = lean_string_append(v___x_1624_, v___x_1625_);
lean_dec_ref(v___x_1625_);
v___x_1627_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1628_ = lean_string_append(v___x_1626_, v___x_1627_);
v___x_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
return v___x_1629_;
}
v___jp_1630_:
{
lean_object* v___x_1633_; uint8_t v___x_1634_; 
v___x_1633_ = lean_unsigned_to_nat(1u);
v___x_1634_ = lean_nat_dec_lt(v___x_1633_, v_major_1632_);
lean_dec(v_major_1632_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1635_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__3));
v___x_1636_ = l_Lake_instOrdSemVerCore_ord(v_ver_1631_, v___x_1635_);
if (v___x_1636_ == 0)
{
v___y_1623_ = v_ver_1631_;
goto v___jp_1622_;
}
else
{
if (v___x_1634_ == 0)
{
lean_object* v___x_1637_; 
v___x_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1637_, 0, v_ver_1631_);
return v___x_1637_;
}
else
{
v___y_1623_ = v_ver_1631_;
goto v___jp_1622_;
}
}
}
else
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1638_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4));
v___x_1639_ = l_Lake_SemVerCore_toString(v_ver_1631_);
v___x_1640_ = lean_string_append(v___x_1638_, v___x_1639_);
lean_dec_ref(v___x_1639_);
v___x_1641_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__5));
v___x_1642_ = lean_string_append(v___x_1640_, v___x_1641_);
v___x_1643_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__1, &l_Lake_Manifest_toJson___closed__1_once, _init_l_Lake_Manifest_toJson___closed__1);
v___x_1644_ = lean_string_append(v___x_1642_, v___x_1643_);
v___x_1645_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__1));
v___x_1646_ = lean_string_append(v___x_1644_, v___x_1645_);
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
return v___x_1647_;
}
}
v___jp_1648_:
{
switch(lean_obj_tag(v_a_1649_))
{
case 2:
{
lean_object* v_n_1650_; lean_object* v_mantissa_1651_; lean_object* v_exponent_1652_; lean_object* v_natZero_1653_; lean_object* v_intZero_1654_; uint8_t v_isNeg_1655_; 
v_n_1650_ = lean_ctor_get(v_a_1649_, 0);
v_mantissa_1651_ = lean_ctor_get(v_n_1650_, 0);
v_exponent_1652_ = lean_ctor_get(v_n_1650_, 1);
v_natZero_1653_ = lean_unsigned_to_nat(0u);
v_intZero_1654_ = lean_obj_once(&l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6, &l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6_once, _init_l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6);
v_isNeg_1655_ = lean_int_dec_lt(v_mantissa_1651_, v_intZero_1654_);
if (v_isNeg_1655_ == 0)
{
uint8_t v___x_1656_; 
v___x_1656_ = lean_nat_dec_eq(v_exponent_1652_, v_natZero_1653_);
if (v___x_1656_ == 0)
{
v_ver_1614_ = v_a_1649_;
goto v___jp_1613_;
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1658_; 
lean_inc(v_mantissa_1651_);
lean_dec_ref_known(v_a_1649_, 1);
v_a_1657_ = lean_nat_abs(v_mantissa_1651_);
lean_dec(v_mantissa_1651_);
v___x_1658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1658_, 0, v_natZero_1653_);
lean_ctor_set(v___x_1658_, 1, v_a_1657_);
lean_ctor_set(v___x_1658_, 2, v_natZero_1653_);
v_ver_1631_ = v___x_1658_;
v_major_1632_ = v_natZero_1653_;
goto v___jp_1630_;
}
}
else
{
v_ver_1614_ = v_a_1649_;
goto v___jp_1613_;
}
}
case 3:
{
lean_object* v_s_1659_; lean_object* v___x_1660_; 
v_s_1659_ = lean_ctor_get(v_a_1649_, 0);
lean_inc_ref(v_s_1659_);
lean_dec_ref_known(v_a_1649_, 1);
v___x_1660_ = l_Lake_StdVer_parse(v_s_1659_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1660_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1660_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
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
lean_object* v_a_1669_; lean_object* v_toSemVerCore_1670_; lean_object* v_major_1671_; 
v_a_1669_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v___x_1660_, 1);
v_toSemVerCore_1670_ = lean_ctor_get(v_a_1669_, 0);
lean_inc_ref(v_toSemVerCore_1670_);
lean_dec(v_a_1669_);
v_major_1671_ = lean_ctor_get(v_toSemVerCore_1670_, 0);
lean_inc(v_major_1671_);
v_ver_1631_ = v_toSemVerCore_1670_;
v_major_1632_ = v_major_1671_;
goto v___jp_1630_;
}
}
default: 
{
v_ver_1614_ = v_a_1649_;
goto v___jp_1613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___boxed(lean_object* v_obj_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_obj_1679_);
lean_dec(v_obj_1679_);
return v_res_1680_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(size_t v_sz_1681_, size_t v_i_1682_, lean_object* v_bs_1683_){
_start:
{
uint8_t v___x_1684_; 
v___x_1684_ = lean_usize_dec_lt(v_i_1682_, v_sz_1681_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1685_, 0, v_bs_1683_);
return v___x_1685_;
}
else
{
lean_object* v_v_1686_; lean_object* v___x_1687_; 
v_v_1686_ = lean_array_uget_borrowed(v_bs_1683_, v_i_1682_);
lean_inc(v_v_1686_);
v___x_1687_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson(v_v_1686_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_dec_ref(v_bs_1683_);
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1687_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1697_; lean_object* v_bs_x27_1698_; size_t v___x_1699_; size_t v___x_1700_; lean_object* v___x_1701_; 
v_a_1696_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1696_);
lean_dec_ref_known(v___x_1687_, 1);
v___x_1697_ = lean_unsigned_to_nat(0u);
v_bs_x27_1698_ = lean_array_uset(v_bs_1683_, v_i_1682_, v___x_1697_);
v___x_1699_ = ((size_t)1ULL);
v___x_1700_ = lean_usize_add(v_i_1682_, v___x_1699_);
v___x_1701_ = lean_array_uset(v_bs_x27_1698_, v_i_1682_, v_a_1696_);
v_i_1682_ = v___x_1700_;
v_bs_1683_ = v___x_1701_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1681_ = stack[0].m_num;
size_t v_i_1682_ = stack[1].m_num;
lean_object* v_bs_1683_ = stack[2].m_obj;
lean_object* v_res_1703_;
v_res_1703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(v_sz_1681_, v_i_1682_, v_bs_1683_);
stack->m_obj
 = v_res_1703_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(size_t v_sz_1745_, size_t v_i_1746_, lean_object* v_bs_1747_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1745_ = stack[0].m_num;
size_t v_i_1746_ = stack[1].m_num;
lean_object* v_bs_1747_ = stack[2].m_obj;
lean_object* v_res_1767_;
v_res_1767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(v_sz_1745_, v_i_1746_, v_bs_1747_);
stack->m_obj
 = v_res_1767_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_1768_, lean_object* v_i_1769_, lean_object* v_bs_1770_){
_start:
{
size_t v_sz_boxed_1771_; size_t v_i_boxed_1772_; lean_object* v_res_1773_; 
v_sz_boxed_1771_ = lean_unbox_usize(v_sz_1768_);
lean_dec(v_sz_1768_);
v_i_boxed_1772_ = lean_unbox_usize(v_i_1769_);
lean_dec(v_i_1769_);
v_res_1773_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(v_sz_boxed_1771_, v_i_boxed_1772_, v_bs_1770_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1(lean_object* v_x_1774_){
_start:
{
if (lean_obj_tag(v_x_1774_) == 4)
{
lean_object* v_elems_1775_; size_t v_sz_1776_; size_t v___x_1777_; lean_object* v___x_1778_; 
v_elems_1775_ = lean_ctor_get(v_x_1774_, 0);
lean_inc_ref(v_elems_1775_);
lean_dec_ref_known(v_x_1774_, 1);
v_sz_1776_ = lean_array_size(v_elems_1775_);
v___x_1777_ = ((size_t)0ULL);
v___x_1778_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(v_sz_1776_, v___x_1777_, v_elems_1775_);
return v___x_1778_;
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1779_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3___closed__0));
v___x_1780_ = lean_unsigned_to_nat(80u);
v___x_1781_ = l_Lean_Json_pretty(v_x_1774_, v___x_1780_);
v___x_1782_ = lean_string_append(v___x_1779_, v___x_1781_);
lean_dec_ref(v___x_1781_);
v___x_1783_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2));
v___x_1784_ = lean_string_append(v___x_1782_, v___x_1783_);
v___x_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
return v___x_1785_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1(lean_object* v_x_1788_){
_start:
{
if (lean_obj_tag(v_x_1788_) == 0)
{
lean_object* v___x_1789_; 
v___x_1789_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1___closed__0));
return v___x_1789_;
}
else
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1(v_x_1788_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1790_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1807_; 
v_a_1799_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1801_ = v___x_1790_;
v_isShared_1802_ = v_isSharedCheck_1807_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1790_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1807_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1803_, 0, v_a_1799_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1803_);
v___x_1805_ = v___x_1801_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(size_t v_sz_1808_, size_t v_i_1809_, lean_object* v_bs_1810_){
_start:
{
uint8_t v___x_1811_; 
v___x_1811_ = lean_usize_dec_lt(v_i_1809_, v_sz_1808_);
if (v___x_1811_ == 0)
{
return v_bs_1810_;
}
else
{
lean_object* v_v_1812_; lean_object* v___x_1813_; lean_object* v_bs_x27_1814_; lean_object* v___x_1815_; size_t v___x_1816_; size_t v___x_1817_; lean_object* v___x_1818_; 
v_v_1812_ = lean_array_uget(v_bs_1810_, v_i_1809_);
v___x_1813_ = lean_unsigned_to_nat(0u);
v_bs_x27_1814_ = lean_array_uset(v_bs_1810_, v_i_1809_, v___x_1813_);
v___x_1815_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(v_v_1812_);
lean_dec(v_v_1812_);
v___x_1816_ = ((size_t)1ULL);
v___x_1817_ = lean_usize_add(v_i_1809_, v___x_1816_);
v___x_1818_ = lean_array_uset(v_bs_x27_1814_, v_i_1809_, v___x_1815_);
v_i_1809_ = v___x_1817_;
v_bs_1810_ = v___x_1818_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1808_ = stack[0].m_num;
size_t v_i_1809_ = stack[1].m_num;
lean_object* v_bs_1810_ = stack[2].m_obj;
lean_object* v_res_1820_;
v_res_1820_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(v_sz_1808_, v_i_1809_, v_bs_1810_);
stack->m_obj
 = v_res_1820_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0___boxed(lean_object* v_sz_1821_, lean_object* v_i_1822_, lean_object* v_bs_1823_){
_start:
{
size_t v_sz_boxed_1824_; size_t v_i_boxed_1825_; lean_object* v_res_1826_; 
v_sz_boxed_1824_ = lean_unbox_usize(v_sz_1821_);
lean_dec(v_sz_1821_);
v_i_boxed_1825_ = lean_unbox_usize(v_i_1822_);
lean_dec(v_i_1822_);
v_res_1826_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(v_sz_boxed_1824_, v_i_boxed_1825_, v_bs_1823_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(lean_object* v_ver_1840_, lean_object* v_obj_1841_){
_start:
{
lean_object* v_a_1843_; lean_object* v___x_1852_; uint8_t v___x_1853_; 
v___x_1852_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__4));
v___x_1853_ = l_Lake_StdVer_compare(v_ver_1840_, v___x_1852_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__7));
v___x_1855_ = l_Lake_JsonObject_getJson_x3f(v_obj_1841_, v___x_1854_);
if (lean_obj_tag(v___x_1855_) == 0)
{
goto v___jp_1848_;
}
else
{
lean_object* v_val_1856_; lean_object* v___x_1857_; 
v_val_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_val_1856_);
lean_dec_ref_known(v___x_1855_, 1);
v___x_1857_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2(v_val_1856_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1867_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1860_ = v___x_1857_;
v_isShared_1861_ = v_isSharedCheck_1867_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1857_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1867_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1865_; 
v___x_1862_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5));
v___x_1863_ = lean_string_append(v___x_1862_, v_a_1858_);
lean_dec(v_a_1858_);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 0, v___x_1863_);
v___x_1865_ = v___x_1860_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1863_);
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
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
v_a_1868_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1857_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1857_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
lean_ctor_set_tag(v___x_1870_, 0);
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
else
{
lean_object* v_a_1876_; 
v_a_1876_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_a_1876_);
lean_dec_ref_known(v___x_1857_, 1);
if (lean_obj_tag(v_a_1876_) == 0)
{
goto v___jp_1848_;
}
else
{
lean_object* v_val_1877_; 
v_val_1877_ = lean_ctor_get(v_a_1876_, 0);
lean_inc(v_val_1877_);
lean_dec_ref_known(v_a_1876_, 1);
v_a_1843_ = v_val_1877_;
goto v___jp_1842_;
}
}
}
}
}
else
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__7));
v___x_1879_ = l_Lake_JsonObject_getJson_x3f(v_obj_1841_, v___x_1878_);
if (lean_obj_tag(v___x_1879_) == 0)
{
goto v___jp_1850_;
}
else
{
lean_object* v_val_1880_; lean_object* v___x_1881_; 
v_val_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_val_1880_);
lean_dec_ref_known(v___x_1879_, 1);
v___x_1881_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1(v_val_1880_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1891_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1884_ = v___x_1881_;
v_isShared_1885_ = v_isSharedCheck_1891_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1881_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1891_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1886_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5));
v___x_1887_ = lean_string_append(v___x_1886_, v_a_1882_);
lean_dec(v_a_1882_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v___x_1887_);
v___x_1889_ = v___x_1884_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1887_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
else
{
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
v_a_1892_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___x_1881_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1881_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
lean_ctor_set_tag(v___x_1894_, 0);
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1892_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1908_; 
v_a_1900_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1902_ = v___x_1881_;
v_isShared_1903_ = v_isSharedCheck_1908_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1881_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1908_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
if (lean_obj_tag(v_a_1900_) == 0)
{
lean_del_object(v___x_1902_);
goto v___jp_1850_;
}
else
{
lean_object* v_val_1904_; lean_object* v___x_1906_; 
v_val_1904_ = lean_ctor_get(v_a_1900_, 0);
lean_inc(v_val_1904_);
lean_dec_ref_known(v_a_1900_, 1);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v_val_1904_);
v___x_1906_ = v___x_1902_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_val_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
}
}
}
v___jp_1842_:
{
size_t v_sz_1844_; size_t v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v_sz_1844_ = lean_array_size(v_a_1843_);
v___x_1845_ = ((size_t)0ULL);
v___x_1846_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(v_sz_1844_, v___x_1845_, v_a_1843_);
v___x_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
return v___x_1847_;
}
v___jp_1848_:
{
lean_object* v___x_1849_; 
v___x_1849_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__0));
v_a_1843_ = v___x_1849_;
goto v___jp_1842_;
}
v___jp_1850_:
{
lean_object* v___x_1851_; 
v___x_1851_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__2));
return v___x_1851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___boxed(lean_object* v_ver_1909_, lean_object* v_obj_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(v_ver_1909_, v_obj_1910_);
lean_dec(v_obj_1910_);
lean_dec_ref(v_ver_1909_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0(lean_object* v_x_1914_){
_start:
{
if (lean_obj_tag(v_x_1914_) == 0)
{
lean_object* v___x_1915_; 
v___x_1915_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0___closed__0));
return v___x_1915_;
}
else
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Lean_Name_fromJson_x3f(v_x_1914_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
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
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1933_; 
v_a_1925_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1927_ = v___x_1916_;
v_isShared_1928_ = v_isSharedCheck_1933_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1916_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1933_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1929_, 0, v_a_1925_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1929_);
v___x_1931_ = v___x_1927_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1929_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_fromJson_x3f(lean_object* v_json_1937_){
_start:
{
lean_object* v___x_1938_; 
v___x_1938_ = l_Lean_Json_getObj_x3f(v_json_1937_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1938_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1948_; 
v_a_1947_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1938_, 1);
v___x_1948_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_a_1947_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec(v_a_1947_);
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1948_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___y_1959_; lean_object* v___y_1960_; uint8_t v___y_1961_; lean_object* v_a_1962_; lean_object* v___y_1984_; uint8_t v___y_1985_; lean_object* v_a_1986_; lean_object* v___y_2012_; uint8_t v___y_2013_; uint8_t v___y_2016_; lean_object* v_a_2017_; uint8_t v___y_2043_; uint8_t v_a_2046_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v_a_1957_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___x_1948_, 1);
v___x_2073_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__4));
v___x_2074_ = l_Lake_JsonObject_getJson_x3f(v_a_1947_, v___x_2073_);
if (lean_obj_tag(v___x_2074_) == 0)
{
goto v___jp_2071_;
}
else
{
lean_object* v_val_2075_; lean_object* v___x_2076_; 
v_val_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_val_2075_);
lean_dec_ref_known(v___x_2074_, 1);
v___x_2076_ = l_Lean_Option_fromJson_x3f___at___00Lake_PackageEntry_fromJson_x3f_spec__0(v_val_2075_);
lean_dec(v_val_2075_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2086_; 
lean_dec(v_a_1957_);
lean_dec(v_a_1947_);
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2079_ = v___x_2076_;
v_isShared_2080_ = v_isSharedCheck_2086_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2076_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2086_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2084_; 
v___x_2081_ = ((lean_object*)(l_Lake_Manifest_fromJson_x3f___closed__2));
v___x_2082_ = lean_string_append(v___x_2081_, v_a_2077_);
lean_dec(v_a_2077_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 0, v___x_2082_);
v___x_2084_ = v___x_2079_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2082_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
else
{
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec(v_a_1957_);
lean_dec(v_a_1947_);
v_a_2087_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2076_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2076_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set_tag(v___x_2089_, 0);
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
else
{
lean_object* v_a_2095_; 
v_a_2095_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2076_, 1);
if (lean_obj_tag(v_a_2095_) == 0)
{
goto v___jp_2071_;
}
else
{
lean_object* v_val_2096_; uint8_t v___x_2097_; 
v_val_2096_ = lean_ctor_get(v_a_2095_, 0);
lean_inc(v_val_2096_);
lean_dec_ref_known(v_a_2095_, 1);
v___x_2097_ = lean_unbox(v_val_2096_);
lean_dec(v_val_2096_);
v_a_2046_ = v___x_2097_;
goto v___jp_2045_;
}
}
}
}
v___jp_1958_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1963_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1964_, 0, v_a_1957_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(v___x_1964_, v_a_1947_);
lean_dec(v_a_1947_);
lean_dec_ref_known(v___x_1964_, 2);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_dec(v_a_1962_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1965_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1965_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
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
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1982_; 
v_a_1974_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1976_ = v___x_1965_;
v_isShared_1977_ = v_isSharedCheck_1982_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1965_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1982_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1978_; lean_object* v___x_1980_; 
v___x_1978_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1978_, 0, v___y_1960_);
lean_ctor_set(v___x_1978_, 1, v___y_1959_);
lean_ctor_set(v___x_1978_, 2, v_a_1962_);
lean_ctor_set(v___x_1978_, 3, v_a_1974_);
lean_ctor_set_uint8(v___x_1978_, sizeof(void*)*4, v___y_1961_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___x_1978_);
v___x_1980_ = v___x_1976_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1978_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
v___jp_1983_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__6));
v___x_1988_ = l_Lake_JsonObject_getJson_x3f(v_a_1947_, v___x_1987_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v___x_1989_; 
v___x_1989_ = lean_box(0);
v___y_1959_ = v_a_1986_;
v___y_1960_ = v___y_1984_;
v___y_1961_ = v___y_1985_;
v_a_1962_ = v___x_1989_;
goto v___jp_1958_;
}
else
{
lean_object* v_val_1990_; lean_object* v___x_1991_; 
v_val_1990_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_val_1990_);
lean_dec_ref_known(v___x_1988_, 1);
v___x_1991_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_1990_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2001_; 
lean_dec_ref(v_a_1986_);
lean_dec(v___y_1984_);
lean_dec(v_a_1957_);
lean_dec(v_a_1947_);
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1994_ = v___x_1991_;
v_isShared_1995_ = v_isSharedCheck_2001_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1991_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2001_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1999_; 
v___x_1996_ = ((lean_object*)(l_Lake_Manifest_fromJson_x3f___closed__0));
v___x_1997_ = lean_string_append(v___x_1996_, v_a_1992_);
lean_dec(v_a_1992_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v___x_1997_);
v___x_1999_ = v___x_1994_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1997_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
else
{
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
lean_dec_ref(v_a_1986_);
lean_dec(v___y_1984_);
lean_dec(v_a_1957_);
lean_dec(v_a_1947_);
v_a_2002_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1991_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1991_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
lean_ctor_set_tag(v___x_2004_, 0);
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
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
lean_object* v_a_2010_; 
v_a_2010_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_2010_);
lean_dec_ref_known(v___x_1991_, 1);
v___y_1959_ = v_a_1986_;
v___y_1960_ = v___y_1984_;
v___y_1961_ = v___y_1985_;
v_a_1962_ = v_a_2010_;
goto v___jp_1958_;
}
}
}
}
v___jp_2011_:
{
lean_object* v___x_2014_; 
v___x_2014_ = l_Lake_defaultLakeDir;
v___y_1984_ = v___y_2012_;
v___y_1985_ = v___y_2013_;
v_a_1986_ = v___x_2014_;
goto v___jp_1983_;
}
v___jp_2015_:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__5));
v___x_2019_ = l_Lake_JsonObject_getJson_x3f(v_a_1947_, v___x_2018_);
if (lean_obj_tag(v___x_2019_) == 0)
{
v___y_2012_ = v_a_2017_;
v___y_2013_ = v___y_2016_;
goto v___jp_2011_;
}
else
{
lean_object* v_val_2020_; lean_object* v___x_2021_; 
v_val_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_val_2020_);
lean_dec_ref_known(v___x_2019_, 1);
v___x_2021_ = l_Lean_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_2020_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2031_; 
lean_dec(v_a_2017_);
lean_dec(v_a_1957_);
lean_dec(v_a_1947_);
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2024_ = v___x_2021_;
v_isShared_2025_ = v_isSharedCheck_2031_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2021_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2031_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2026_ = ((lean_object*)(l_Lake_Manifest_fromJson_x3f___closed__1));
v___x_2027_ = lean_string_append(v___x_2026_, v_a_2022_);
lean_dec(v_a_2022_);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2027_);
v___x_2029_ = v___x_2024_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
else
{
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec(v_a_2017_);
lean_dec(v_a_1957_);
lean_dec(v_a_1947_);
v_a_2032_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2021_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2021_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set_tag(v___x_2034_, 0);
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
else
{
lean_object* v_a_2040_; 
v_a_2040_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2021_, 1);
if (lean_obj_tag(v_a_2040_) == 0)
{
v___y_2012_ = v_a_2017_;
v___y_2013_ = v___y_2016_;
goto v___jp_2011_;
}
else
{
lean_object* v_val_2041_; 
v_val_2041_ = lean_ctor_get(v_a_2040_, 0);
lean_inc(v_val_2041_);
lean_dec_ref_known(v_a_2040_, 1);
v___y_1984_ = v_a_2017_;
v___y_1985_ = v___y_2016_;
v_a_1986_ = v_val_2041_;
goto v___jp_1983_;
}
}
}
}
}
v___jp_2042_:
{
lean_object* v___x_2044_; 
v___x_2044_ = lean_box(0);
v___y_2016_ = v___y_2043_;
v_a_2017_ = v___x_2044_;
goto v___jp_2015_;
}
v___jp_2045_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6));
v___x_2048_ = l_Lake_JsonObject_getJson_x3f(v_a_1947_, v___x_2047_);
if (lean_obj_tag(v___x_2048_) == 0)
{
v___y_2043_ = v_a_2046_;
goto v___jp_2042_;
}
else
{
lean_object* v_val_2049_; lean_object* v___x_2050_; 
v_val_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_val_2049_);
lean_dec_ref_known(v___x_2048_, 1);
v___x_2050_ = l_Lean_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0(v_val_2049_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_a_1957_);
lean_dec(v_a_1947_);
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2053_ = v___x_2050_;
v_isShared_2054_ = v_isSharedCheck_2060_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2050_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2060_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2055_ = ((lean_object*)(l_Lake_PackageEntry_fromJson_x3f___closed__1));
v___x_2056_ = lean_string_append(v___x_2055_, v_a_2051_);
lean_dec(v_a_2051_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v___x_2056_);
v___x_2058_ = v___x_2053_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
else
{
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec(v_a_1957_);
lean_dec(v_a_1947_);
v_a_2061_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2050_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2050_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
lean_ctor_set_tag(v___x_2063_, 0);
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
else
{
lean_object* v_a_2069_; 
v_a_2069_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2069_);
lean_dec_ref_known(v___x_2050_, 1);
if (lean_obj_tag(v_a_2069_) == 0)
{
v___y_2043_ = v_a_2046_;
goto v___jp_2042_;
}
else
{
lean_object* v_val_2070_; 
v_val_2070_ = lean_ctor_get(v_a_2069_, 0);
lean_inc(v_val_2070_);
lean_dec_ref_known(v_a_2069_, 1);
v___y_2016_ = v_a_2046_;
v_a_2017_ = v_val_2070_;
goto v___jp_2015_;
}
}
}
}
}
v___jp_2071_:
{
uint8_t v___x_2072_; 
v___x_2072_ = 0;
v_a_2046_ = v___x_2072_;
goto v___jp_2045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_parse(lean_object* v_data_2101_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Lean_Json_parse(v_data_2101_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2112_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2105_ = v___x_2102_;
v_isShared_2106_ = v_isSharedCheck_2112_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2102_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2112_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2107_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2108_ = lean_string_append(v___x_2107_, v_a_2103_);
lean_dec(v_a_2103_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 0, v___x_2108_);
v___x_2110_ = v___x_2105_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2114_; 
v_a_2113_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2113_);
lean_dec_ref_known(v___x_2102_, 1);
v___x_2114_ = l_Lake_Manifest_fromJson_x3f(v_a_2113_);
return v___x_2114_;
}
}
}
lean_object* l_Lake_Manifest_load(lean_object* v_file_2116_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_IO_FS_readFile(v_file_2116_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2147_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2147_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2147_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v_a_2124_; lean_object* v___x_2132_; 
v___x_2132_ = l_Lean_Json_parse(v_a_2119_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v___x_2134_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2135_ = lean_string_append(v___x_2134_, v_a_2133_);
lean_dec(v_a_2133_);
v_a_2124_ = v___x_2135_;
goto v___jp_2123_;
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2137_; 
v_a_2136_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2132_, 1);
v___x_2137_ = l_Lake_Manifest_fromJson_x3f(v_a_2136_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v_a_2124_ = v_a_2138_;
goto v___jp_2123_;
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_del_object(v___x_2121_);
lean_dec_ref(v_file_2116_);
v_a_2139_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2137_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2137_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set_tag(v___x_2141_, 0);
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
v___jp_2123_:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2130_; 
v___x_2125_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2126_ = lean_string_append(v_file_2116_, v___x_2125_);
v___x_2127_ = lean_string_append(v___x_2126_, v_a_2124_);
lean_dec_ref(v_a_2124_);
v___x_2128_ = lean_mk_io_user_error(v___x_2127_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set_tag(v___x_2121_, 1);
lean_ctor_set(v___x_2121_, 0, v___x_2128_);
v___x_2130_ = v___x_2121_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec_ref(v_file_2116_);
v_a_2148_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2118_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2118_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
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
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Manifest_load_0interp(lean_interpreter_value* stack)
{
lean_object* v_file_2116_ = stack[0].m_obj;
lean_object* v_res_2156_;
v_res_2156_ = l_Lake_Manifest_load(v_file_2116_);
stack->m_obj
 = v_res_2156_;
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load___boxed(lean_object* v_file_2157_, lean_object* v_a_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Lake_Manifest_load(v_file_2157_);
return v_res_2159_;
}
}
lean_object* l_Lake_Manifest_load_x3f(lean_object* v_file_2160_){
_start:
{
lean_object* v_a_2163_; lean_object* v___x_2167_; 
v___x_2167_ = l_IO_FS_readFile(v_file_2160_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2196_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2170_ = v___x_2167_;
v_isShared_2171_ = v_isSharedCheck_2196_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2167_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2196_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v_a_2173_; lean_object* v___x_2178_; 
v___x_2178_ = l_Lean_Json_parse(v_a_2168_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
lean_del_object(v___x_2170_);
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref_known(v___x_2178_, 1);
v___x_2180_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2181_ = lean_string_append(v___x_2180_, v_a_2179_);
lean_dec(v_a_2179_);
v_a_2173_ = v___x_2181_;
goto v___jp_2172_;
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2183_; 
v_a_2182_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2182_);
lean_dec_ref_known(v___x_2178_, 1);
v___x_2183_ = l_Lake_Manifest_fromJson_x3f(v_a_2182_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; 
lean_del_object(v___x_2170_);
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2184_);
lean_dec_ref_known(v___x_2183_, 1);
v_a_2173_ = v_a_2184_;
goto v___jp_2172_;
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2195_; 
lean_dec_ref(v_file_2160_);
v_a_2185_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2187_ = v___x_2183_;
v_isShared_2188_ = v_isSharedCheck_2195_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2183_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2195_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
lean_object* v___x_2192_; 
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2190_);
v___x_2192_ = v___x_2170_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
}
v___jp_2172_:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2174_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2175_ = lean_string_append(v_file_2160_, v___x_2174_);
v___x_2176_ = lean_string_append(v___x_2175_, v_a_2173_);
lean_dec_ref(v_a_2173_);
v___x_2177_ = lean_mk_io_user_error(v___x_2176_);
v_a_2163_ = v___x_2177_;
goto v___jp_2162_;
}
}
}
else
{
lean_object* v_a_2197_; 
lean_dec_ref(v_file_2160_);
v_a_2197_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2197_);
lean_dec_ref_known(v___x_2167_, 1);
v_a_2163_ = v_a_2197_;
goto v___jp_2162_;
}
v___jp_2162_:
{
if (lean_obj_tag(v_a_2163_) == 11)
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
lean_dec_ref_known(v_a_2163_, 2);
v___x_2164_ = lean_box(0);
v___x_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
return v___x_2165_;
}
else
{
lean_object* v___x_2166_; 
v___x_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2166_, 0, v_a_2163_);
return v___x_2166_;
}
}
}
}
LEAN_EXPORT void l_Lake_Manifest_load_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_file_2160_ = stack[0].m_obj;
lean_object* v_res_2198_;
v_res_2198_ = l_Lake_Manifest_load_x3f(v_file_2160_);
stack->m_obj
 = v_res_2198_;
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f___boxed(lean_object* v_file_2199_, lean_object* v_a_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lake_Manifest_load_x3f(v_file_2199_);
return v_res_2201_;
}
}
lean_object* l_Lake_Manifest_save(lean_object* v_self_2202_, lean_object* v_manifestFile_2203_){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v_contents_2207_; uint32_t v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2205_ = l_Lake_Manifest_toJson(v_self_2202_);
v___x_2206_ = lean_unsigned_to_nat(80u);
v_contents_2207_ = l_Lean_Json_pretty(v___x_2205_, v___x_2206_);
v___x_2208_ = 10;
v___x_2209_ = lean_string_push(v_contents_2207_, v___x_2208_);
v___x_2210_ = l_IO_FS_writeFile(v_manifestFile_2203_, v___x_2209_);
lean_dec_ref(v___x_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT void l_Lake_Manifest_save_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_2202_ = stack[0].m_obj;
lean_object* v_manifestFile_2203_ = stack[1].m_obj;
lean_object* v_res_2211_;
v_res_2211_ = l_Lake_Manifest_save(v_self_2202_, v_manifestFile_2203_);
stack->m_obj
 = v_res_2211_;
}
LEAN_EXPORT lean_object* l_Lake_Manifest_save___boxed(lean_object* v_self_2212_, lean_object* v_manifestFile_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lake_Manifest_save(v_self_2212_, v_manifestFile_2213_);
lean_dec_ref(v_manifestFile_2213_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_decodeEntries(lean_object* v_data_2216_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Lean_Json_getObj_x3f(v_data_2216_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2217_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2217_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2227_; 
v_a_2226_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2226_);
lean_dec_ref_known(v___x_2217_, 1);
v___x_2227_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_a_2226_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec(v_a_2226_);
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2227_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2227_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v_a_2236_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2236_);
lean_dec_ref_known(v___x_2227_, 1);
v___x_2237_ = ((lean_object*)(l_Lake_Manifest_version___closed__1));
v___x_2238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2238_, 0, v_a_2236_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
v___x_2239_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(v___x_2238_, v_a_2226_);
lean_dec(v_a_2226_);
lean_dec_ref_known(v___x_2238_, 2);
return v___x_2239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_parseEntries(lean_object* v_data_2240_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_Json_parse(v_data_2240_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2251_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2244_ = v___x_2241_;
v_isShared_2245_ = v_isSharedCheck_2251_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2241_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2251_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2249_; 
v___x_2246_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2247_ = lean_string_append(v___x_2246_, v_a_2242_);
lean_dec(v_a_2242_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 0, v___x_2247_);
v___x_2249_ = v___x_2244_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2247_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2253_; 
v_a_2252_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_a_2252_);
lean_dec_ref_known(v___x_2241_, 1);
v___x_2253_ = l_Lake_Manifest_decodeEntries(v_a_2252_);
return v___x_2253_;
}
}
}
lean_object* l_Lake_Manifest_loadEntries(lean_object* v_file_2254_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_IO_FS_readFile(v_file_2254_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2285_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2285_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2285_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v_a_2262_; lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_Json_parse(v_a_2257_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2271_);
lean_dec_ref_known(v___x_2270_, 1);
v___x_2272_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2273_ = lean_string_append(v___x_2272_, v_a_2271_);
lean_dec(v_a_2271_);
v_a_2262_ = v___x_2273_;
goto v___jp_2261_;
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2275_; 
v_a_2274_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2274_);
lean_dec_ref_known(v___x_2270_, 1);
v___x_2275_ = l_Lake_Manifest_decodeEntries(v_a_2274_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref_known(v___x_2275_, 1);
v_a_2262_ = v_a_2276_;
goto v___jp_2261_;
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_del_object(v___x_2259_);
lean_dec_ref(v_file_2254_);
v_a_2277_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2275_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2275_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
lean_ctor_set_tag(v___x_2279_, 0);
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
v___jp_2261_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2268_; 
v___x_2263_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2264_ = lean_string_append(v_file_2254_, v___x_2263_);
v___x_2265_ = lean_string_append(v___x_2264_, v_a_2262_);
lean_dec_ref(v_a_2262_);
v___x_2266_ = lean_mk_io_user_error(v___x_2265_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set_tag(v___x_2259_, 1);
lean_ctor_set(v___x_2259_, 0, v___x_2266_);
v___x_2268_ = v___x_2259_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2266_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec_ref(v_file_2254_);
v_a_2286_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2256_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2256_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Manifest_loadEntries_0interp(lean_interpreter_value* stack)
{
lean_object* v_file_2254_ = stack[0].m_obj;
lean_object* v_res_2294_;
v_res_2294_ = l_Lake_Manifest_loadEntries(v_file_2254_);
stack->m_obj
 = v_res_2294_;
}
LEAN_EXPORT lean_object* l_Lake_Manifest_loadEntries___boxed(lean_object* v_file_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lake_Manifest_loadEntries(v_file_2295_);
return v_res_2297_;
}
}
lean_object* l_Lake_Manifest_tryLoadEntries(lean_object* v_file_2298_){
_start:
{
lean_object* v_a_2301_; lean_object* v___x_2310_; 
v___x_2310_ = l_IO_FS_readFile(v_file_2298_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2332_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2313_ = v___x_2310_;
v_isShared_2314_ = v_isSharedCheck_2332_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2310_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2332_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v_a_2316_; lean_object* v___x_2321_; 
v___x_2321_ = l_Lean_Json_parse(v_a_2311_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
lean_del_object(v___x_2313_);
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
lean_dec_ref_known(v___x_2321_, 1);
v___x_2323_ = ((lean_object*)(l_Lake_Manifest_parse___closed__0));
v___x_2324_ = lean_string_append(v___x_2323_, v_a_2322_);
lean_dec(v_a_2322_);
v_a_2316_ = v___x_2324_;
goto v___jp_2315_;
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2326_; 
v_a_2325_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2325_);
lean_dec_ref_known(v___x_2321_, 1);
v___x_2326_ = l_Lake_Manifest_decodeEntries(v_a_2325_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; 
lean_del_object(v___x_2313_);
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2327_);
lean_dec_ref_known(v___x_2326_, 1);
v_a_2316_ = v_a_2327_;
goto v___jp_2315_;
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; 
lean_dec_ref(v_file_2298_);
v_a_2328_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2328_);
lean_dec_ref_known(v___x_2326_, 1);
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 0, v_a_2328_);
v___x_2330_ = v___x_2313_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2328_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
v___jp_2315_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2317_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
lean_inc_ref(v_file_2298_);
v___x_2318_ = lean_string_append(v_file_2298_, v___x_2317_);
v___x_2319_ = lean_string_append(v___x_2318_, v_a_2316_);
lean_dec_ref(v_a_2316_);
v___x_2320_ = lean_mk_io_user_error(v___x_2319_);
v_a_2301_ = v___x_2320_;
goto v___jp_2300_;
}
}
}
else
{
lean_object* v_a_2333_; 
v_a_2333_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2310_, 1);
v_a_2301_ = v_a_2333_;
goto v___jp_2300_;
}
v___jp_2300_:
{
if (lean_obj_tag(v_a_2301_) == 11)
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
lean_dec_ref_known(v_a_2301_, 2);
lean_dec_ref(v_file_2298_);
v___x_2302_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__1));
v___x_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
return v___x_2303_;
}
else
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2304_ = ((lean_object*)(l_Lake_Manifest_load___closed__0));
v___x_2305_ = lean_string_append(v_file_2298_, v___x_2304_);
v___x_2306_ = lean_io_error_to_string(v_a_2301_);
v___x_2307_ = lean_string_append(v___x_2305_, v___x_2306_);
lean_dec_ref(v___x_2306_);
v___x_2308_ = lean_mk_io_user_error(v___x_2307_);
v___x_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
return v___x_2309_;
}
}
}
}
LEAN_EXPORT void l_Lake_Manifest_tryLoadEntries_0interp(lean_interpreter_value* stack)
{
lean_object* v_file_2298_ = stack[0].m_obj;
lean_object* v_res_2334_;
v_res_2334_ = l_Lake_Manifest_tryLoadEntries(v_file_2298_);
stack->m_obj
 = v_res_2334_;
}
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries___boxed(lean_object* v_file_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lake_Manifest_tryLoadEntries(v_file_2335_);
return v_res_2337_;
}
}
static lean_object* _init_l_Lake_Manifest_saveEntries___closed__0(void){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2338_ = lean_obj_once(&l_Lake_Manifest_toJson___closed__2, &l_Lake_Manifest_toJson___closed__2_once, _init_l_Lake_Manifest_toJson___closed__2);
v___x_2339_ = ((lean_object*)(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7));
v___x_2340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2339_);
lean_ctor_set(v___x_2340_, 1, v___x_2338_);
return v___x_2340_;
}
}
lean_object* l_Lake_Manifest_saveEntries(lean_object* v_file_2341_, lean_object* v_entries_2342_){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v_contents_2353_; uint32_t v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2344_ = lean_obj_once(&l_Lake_Manifest_saveEntries___closed__0, &l_Lake_Manifest_saveEntries___closed__0_once, _init_l_Lake_Manifest_saveEntries___closed__0);
v___x_2345_ = ((lean_object*)(l_Lake_Manifest_toJson___closed__7));
v___x_2346_ = l_Lean_Array_toJson___at___00Lake_Manifest_toJson_spec__0(v_entries_2342_);
v___x_2347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2345_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
v___x_2348_ = lean_box(0);
v___x_2349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2347_);
lean_ctor_set(v___x_2349_, 1, v___x_2348_);
v___x_2350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2344_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
v___x_2351_ = l_Lean_Json_mkObj(v___x_2350_);
lean_dec_ref_known(v___x_2350_, 2);
v___x_2352_ = lean_unsigned_to_nat(80u);
v_contents_2353_ = l_Lean_Json_pretty(v___x_2351_, v___x_2352_);
v___x_2354_ = 10;
v___x_2355_ = lean_string_push(v_contents_2353_, v___x_2354_);
v___x_2356_ = l_IO_FS_writeFile(v_file_2341_, v___x_2355_);
lean_dec_ref(v___x_2355_);
return v___x_2356_;
}
}
LEAN_EXPORT void l_Lake_Manifest_saveEntries_0interp(lean_interpreter_value* stack)
{
lean_object* v_file_2341_ = stack[0].m_obj;
lean_object* v_entries_2342_ = stack[1].m_obj;
lean_object* v_res_2357_;
v_res_2357_ = l_Lake_Manifest_saveEntries(v_file_2341_, v_entries_2342_);
stack->m_obj
 = v_res_2357_;
}
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries___boxed(lean_object* v_file_2358_, lean_object* v_entries_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l_Lake_Manifest_saveEntries(v_file_2358_, v_entries_2359_);
lean_dec_ref(v_file_2358_);
return v_res_2361_;
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
