// Lean compiler output
// Module: Lake.Config.Package
// Imports: public import Lake.Config.Cache public import Lake.Config.Script public import Lake.Config.ConfigDecl public import Lake.Config.Dependency public import Lake.Config.PackageConfig public import Lake.Util.FilePath public import Lake.Util.OrdHashSet public import Lake.Util.Name meta import all Lake.Util.OpaqueType import Lake.Util.OpaqueType import Lake.Util.IO
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
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lake_LeanExe_keyword;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lake_LeanLibConfig_isBuildableModule___redArg(lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lake_CacheServiceScope_ofString(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_OrdHashSet_empty(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instInhabitedPackageConfig_default(lean_object*, lean_object*);
extern lean_object* l_System_instInhabitedFilePath_default;
lean_object* l_Lean_LeanOptions_appendArray(lean_object*, lean_object*);
uint8_t l_Lake_LeanLibConfig_isLocalModule___redArg(lean_object*, lean_object*);
lean_object* l_instDecidableEqBool___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lake_removeDirAllIfExists(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType___boxed(lean_object*);
static lean_once_cell_t l_Lake_instInhabitedPackage_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPackage_default___closed__0;
static const lean_string_object l_Lake_instInhabitedPackage_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedPackage_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedPackage_default___closed__1_value;
static const lean_array_object l_Lake_instInhabitedPackage_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instInhabitedPackage_default___closed__2 = (const lean_object*)&l_Lake_instInhabitedPackage_default___closed__2_value;
static lean_once_cell_t l_Lake_instInhabitedPackage_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPackage_default___closed__3;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackage_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackage;
static lean_once_cell_t l_Lake_Package_instHashable___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lake_Package_instHashable___lam__0___closed__0;
LEAN_EXPORT uint64_t l_Lake_Package_instHashable___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_instHashable___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_Package_instHashable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Package_instHashable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_instHashable___closed__0 = (const lean_object*)&l_Lake_Package_instHashable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Package_instHashable = (const lean_object*)&l_Lake_Package_instHashable___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_Package_instBEq___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_instBEq___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Package_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Package_instBEq___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_instBEq___closed__0 = (const lean_object*)&l_Lake_Package_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Package_instBEq = (const lean_object*)&l_Lake_Package_instBEq___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Package_prettyName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_instQueryJson___lam__0(lean_object*);
static const lean_closure_object l_Lake_Package_instQueryJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Package_instQueryJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_instQueryJson___closed__0 = (const lean_object*)&l_Lake_Package_instQueryJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Package_instQueryJson = (const lean_object*)&l_Lake_Package_instQueryJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Package_instQueryText___lam__0(lean_object*);
static const lean_closure_object l_Lake_Package_instQueryText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Package_instQueryText___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_instQueryText___closed__0 = (const lean_object*)&l_Lake_Package_instQueryText___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Package_instQueryText = (const lean_object*)&l_Lake_Package_instQueryText___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Package_name(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_name___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_reservoirName(lean_object*);
static lean_once_cell_t l_Lake_PackageSet_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageSet_empty___closed__0;
static lean_once_cell_t l_Lake_PackageSet_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PackageSet_empty___closed__1;
LEAN_EXPORT lean_object* l_Lake_PackageSet_empty;
static lean_once_cell_t l_Lake_OrdPackageSet_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrdPackageSet_empty___closed__0;
LEAN_EXPORT lean_object* l_Lake_OrdPackageSet_empty;
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_NPackage_instCoeOutPackage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_NPackage_instCoeOutPackage___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_NPackage_instCoeOutPackage___closed__0 = (const lean_object*)&l_Lake_NPackage_instCoeOutPackage___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeDepPackageKeyName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeDepPackageKeyName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instInhabitedPostUpdateHook_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instInhabitedPostUpdateHook_default___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instInhabitedPostUpdateHook_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedPostUpdateHook_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeMk(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeGet(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_instImpl___closed__0_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_instImpl___closed__0_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12_ = (const lean_object*)&l_Lake_instImpl___closed__0_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value;
static const lean_string_object l_Lake_instImpl___closed__1_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "PostUpdateHookDecl"};
static const lean_object* l_Lake_instImpl___closed__1_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12_ = (const lean_object*)&l_Lake_instImpl___closed__1_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value;
static const lean_ctor_object l_Lake_instImpl___closed__2_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instImpl___closed__0_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_instImpl___closed__2_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value_aux_0),((lean_object*)&l_Lake_instImpl___closed__1_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(197, 83, 199, 129, 62, 183, 64, 19)}};
static const lean_object* l_Lake_instImpl___closed__2_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12_ = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value;
LEAN_EXPORT const lean_object* l_Lake_instImpl_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12_ = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNamePostUpdateHookDecl = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value;
LEAN_EXPORT uint8_t l_Lake_Package_isRoot(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_isRoot___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_bootstrap(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_bootstrap___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_id_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_version(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_version___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_versionTags(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_versionTags___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_description(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_description___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_keywords(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_keywords___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_homepage(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_homepage___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_reservoir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_reservoir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_license(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_license___boxed(lean_object*);
static const lean_closure_object l_Lake_Package_relLicenseFiles___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_System_FilePath_normalize, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_relLicenseFiles___closed__0 = (const lean_object*)&l_Lake_Package_relLicenseFiles___closed__0_value;
static const lean_closure_object l_Lake_Package_relLicenseFiles___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_relLicenseFiles___closed__1 = (const lean_object*)&l_Lake_Package_relLicenseFiles___closed__1_value;
static const lean_closure_object l_Lake_Package_relLicenseFiles___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_relLicenseFiles___closed__2 = (const lean_object*)&l_Lake_Package_relLicenseFiles___closed__2_value;
static const lean_closure_object l_Lake_Package_relLicenseFiles___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_relLicenseFiles___closed__3 = (const lean_object*)&l_Lake_Package_relLicenseFiles___closed__3_value;
static const lean_closure_object l_Lake_Package_relLicenseFiles___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_relLicenseFiles___closed__4 = (const lean_object*)&l_Lake_Package_relLicenseFiles___closed__4_value;
static const lean_closure_object l_Lake_Package_relLicenseFiles___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_relLicenseFiles___closed__5 = (const lean_object*)&l_Lake_Package_relLicenseFiles___closed__5_value;
static const lean_closure_object l_Lake_Package_relLicenseFiles___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_relLicenseFiles___closed__6 = (const lean_object*)&l_Lake_Package_relLicenseFiles___closed__6_value;
static const lean_closure_object l_Lake_Package_relLicenseFiles___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_relLicenseFiles___closed__7 = (const lean_object*)&l_Lake_Package_relLicenseFiles___closed__7_value;
static const lean_ctor_object l_Lake_Package_relLicenseFiles___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Package_relLicenseFiles___closed__1_value),((lean_object*)&l_Lake_Package_relLicenseFiles___closed__2_value)}};
static const lean_object* l_Lake_Package_relLicenseFiles___closed__8 = (const lean_object*)&l_Lake_Package_relLicenseFiles___closed__8_value;
static const lean_ctor_object l_Lake_Package_relLicenseFiles___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Package_relLicenseFiles___closed__8_value),((lean_object*)&l_Lake_Package_relLicenseFiles___closed__3_value),((lean_object*)&l_Lake_Package_relLicenseFiles___closed__4_value),((lean_object*)&l_Lake_Package_relLicenseFiles___closed__5_value),((lean_object*)&l_Lake_Package_relLicenseFiles___closed__6_value)}};
static const lean_object* l_Lake_Package_relLicenseFiles___closed__9 = (const lean_object*)&l_Lake_Package_relLicenseFiles___closed__9_value;
static const lean_ctor_object l_Lake_Package_relLicenseFiles___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Package_relLicenseFiles___closed__9_value),((lean_object*)&l_Lake_Package_relLicenseFiles___closed__7_value)}};
static const lean_object* l_Lake_Package_relLicenseFiles___closed__10 = (const lean_object*)&l_Lake_Package_relLicenseFiles___closed__10_value;
LEAN_EXPORT lean_object* l_Lake_Package_relLicenseFiles(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_relReadmeFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_readmeFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_lakeDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_relPkgsDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_pkgsDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_manifestFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent___boxed(lean_object*);
static lean_once_cell_t l_Lake_Package_isPlatformIndependent___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_isPlatformIndependent___closed__0;
static const lean_ctor_object l_Lake_Package_isPlatformIndependent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_Package_isPlatformIndependent___closed__1 = (const lean_object*)&l_Lake_Package_isPlatformIndependent___closed__1_value;
LEAN_EXPORT uint8_t l_Lake_Package_isPlatformIndependent(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_isPlatformIndependent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildArchiveFile(lean_object*);
static const lean_string_object l_Lake_Package_barrelFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "build.barrel"};
static const lean_object* l_Lake_Package_barrelFile___closed__0 = (const lean_object*)&l_Lake_Package_barrelFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Package_barrelFile(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_preferReleaseBuild(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_preferReleaseBuild___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_precompileModules(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_precompileModules___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_buildType(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildType___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_backend(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_backend___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_allowImportAll(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_allowImportAll___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_plugins(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_plugins___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_srcDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_rootDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_leanLibDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_staticLibDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_sharedLibDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_binDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_irDir(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_libPrefixOnWindows(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_libPrefixOnWindows___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_cacheScope(lean_object*);
static const lean_string_object l___private_Lake_Config_Package_0__Lake_Package_reservoirScope___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Lake_Config_Package_0__Lake_Package_reservoirScope___closed__0 = (const lean_object*)&l___private_Lake_Config_Package_0__Lake_Package_reservoirScope___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_reservoirScope_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_lib"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_isLocalModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_isLocalModule___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_isBuildableModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_isBuildableModule___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_clean(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_clean___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType(lean_object* v_pkg_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType___boxed(lean_object* v_pkg_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType(v_pkg_3_);
lean_dec(v_pkg_3_);
return v_res_4_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__0(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_box(0);
v___x_6_ = l_Lake_instInhabitedPackageConfig_default(v___x_5_, v___x_5_);
return v___x_6_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__3(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_10_ = lean_box(0);
v___x_11_ = lean_box(1);
v___x_12_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__2));
v___x_13_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__1));
v___x_14_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__0, &l_Lake_instInhabitedPackage_default___closed__0_once, _init_l_Lake_instInhabitedPackage_default___closed__0);
v___x_15_ = l_System_instInhabitedFilePath_default;
v___x_16_ = lean_box(0);
v___x_17_ = lean_unsigned_to_nat(0u);
v___x_18_ = lean_alloc_ctor(0, 24, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
lean_ctor_set(v___x_18_, 1, v___x_16_);
lean_ctor_set(v___x_18_, 2, v___x_16_);
lean_ctor_set(v___x_18_, 3, v___x_16_);
lean_ctor_set(v___x_18_, 4, v___x_15_);
lean_ctor_set(v___x_18_, 5, v___x_15_);
lean_ctor_set(v___x_18_, 6, v___x_14_);
lean_ctor_set(v___x_18_, 7, v___x_15_);
lean_ctor_set(v___x_18_, 8, v___x_15_);
lean_ctor_set(v___x_18_, 9, v___x_15_);
lean_ctor_set(v___x_18_, 10, v___x_13_);
lean_ctor_set(v___x_18_, 11, v___x_13_);
lean_ctor_set(v___x_18_, 12, v___x_12_);
lean_ctor_set(v___x_18_, 13, v___x_12_);
lean_ctor_set(v___x_18_, 14, v___x_11_);
lean_ctor_set(v___x_18_, 15, v___x_12_);
lean_ctor_set(v___x_18_, 16, v___x_11_);
lean_ctor_set(v___x_18_, 17, v___x_12_);
lean_ctor_set(v___x_18_, 18, v___x_12_);
lean_ctor_set(v___x_18_, 19, v___x_13_);
lean_ctor_set(v___x_18_, 20, v___x_13_);
lean_ctor_set(v___x_18_, 21, v___x_13_);
lean_ctor_set(v___x_18_, 22, v___x_10_);
lean_ctor_set(v___x_18_, 23, v___x_10_);
return v___x_18_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default(void){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__3, &l_Lake_instInhabitedPackage_default___closed__3_once, _init_l_Lake_instInhabitedPackage_default___closed__3);
return v___x_19_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage(void){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lake_instInhabitedPackage_default;
return v___x_20_;
}
}
static uint64_t _init_l_Lake_Package_instHashable___lam__0___closed__0(void){
_start:
{
lean_object* v___x_21_; uint64_t v___x_22_; 
v___x_21_ = lean_unsigned_to_nat(1723u);
v___x_22_ = lean_uint64_of_nat(v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT uint64_t l_Lake_Package_instHashable___lam__0(lean_object* v_pkg_23_){
_start:
{
lean_object* v_keyName_24_; 
v_keyName_24_ = lean_ctor_get(v_pkg_23_, 2);
if (lean_obj_tag(v_keyName_24_) == 0)
{
uint64_t v___x_25_; 
v___x_25_ = lean_uint64_once(&l_Lake_Package_instHashable___lam__0___closed__0, &l_Lake_Package_instHashable___lam__0___closed__0_once, _init_l_Lake_Package_instHashable___lam__0___closed__0);
return v___x_25_;
}
else
{
uint64_t v_hash_26_; 
v_hash_26_ = lean_ctor_get_uint64(v_keyName_24_, sizeof(void*)*2);
return v_hash_26_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instHashable___lam__0___boxed(lean_object* v_pkg_27_){
_start:
{
uint64_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l_Lake_Package_instHashable___lam__0(v_pkg_27_);
lean_dec_ref(v_pkg_27_);
v_r_29_ = lean_box_uint64(v_res_28_);
return v_r_29_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_instBEq___lam__0(lean_object* v_p1_32_, lean_object* v_p2_33_){
_start:
{
lean_object* v_wsIdx_34_; lean_object* v_wsIdx_35_; uint8_t v___x_36_; 
v_wsIdx_34_ = lean_ctor_get(v_p1_32_, 0);
v_wsIdx_35_ = lean_ctor_get(v_p2_33_, 0);
v___x_36_ = lean_nat_dec_eq(v_wsIdx_34_, v_wsIdx_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instBEq___lam__0___boxed(lean_object* v_p1_37_, lean_object* v_p2_38_){
_start:
{
uint8_t v_res_39_; lean_object* v_r_40_; 
v_res_39_ = l_Lake_Package_instBEq___lam__0(v_p1_37_, v_p2_38_);
lean_dec_ref(v_p2_38_);
lean_dec_ref(v_p1_37_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_prettyName(lean_object* v_self_43_){
_start:
{
lean_object* v_baseName_44_; uint8_t v___x_45_; lean_object* v___x_46_; 
v_baseName_44_ = lean_ctor_get(v_self_43_, 1);
lean_inc(v_baseName_44_);
lean_dec_ref(v_self_43_);
v___x_45_ = 0;
v___x_46_ = l_Lean_Name_toString(v_baseName_44_, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instQueryJson___lam__0(lean_object* v_x_47_){
_start:
{
lean_object* v_keyName_48_; uint8_t v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v_keyName_48_ = lean_ctor_get(v_x_47_, 2);
lean_inc(v_keyName_48_);
lean_dec_ref(v_x_47_);
v___x_49_ = 1;
v___x_50_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_keyName_48_, v___x_49_);
v___x_51_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instQueryText___lam__0(lean_object* v_x_54_){
_start:
{
lean_object* v_baseName_55_; uint8_t v___x_56_; lean_object* v___x_57_; 
v_baseName_55_ = lean_ctor_get(v_x_54_, 1);
lean_inc(v_baseName_55_);
lean_dec_ref(v_x_54_);
v___x_56_ = 0;
v___x_57_ = l_Lean_Name_toString(v_baseName_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_name(lean_object* v_self_60_){
_start:
{
lean_object* v_baseName_61_; 
v_baseName_61_ = lean_ctor_get(v_self_60_, 1);
lean_inc(v_baseName_61_);
return v_baseName_61_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_name___boxed(lean_object* v_self_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lake_Package_name(v_self_62_);
lean_dec_ref(v_self_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirName(lean_object* v_self_64_){
_start:
{
lean_object* v_origName_65_; uint8_t v___x_66_; lean_object* v___x_67_; 
v_origName_65_ = lean_ctor_get(v_self_64_, 3);
lean_inc(v_origName_65_);
lean_dec_ref(v_self_64_);
v___x_66_ = 0;
v___x_67_ = l_Lean_Name_toString(v_origName_65_, v___x_66_);
return v___x_67_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty___closed__0(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_box(0);
v___x_69_ = lean_unsigned_to_nat(16u);
v___x_70_ = lean_mk_array(v___x_69_, v___x_68_);
return v___x_70_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty___closed__1(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_71_ = lean_obj_once(&l_Lake_PackageSet_empty___closed__0, &l_Lake_PackageSet_empty___closed__0_once, _init_l_Lake_PackageSet_empty___closed__0);
v___x_72_ = lean_unsigned_to_nat(0u);
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_71_);
return v___x_73_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty(void){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_obj_once(&l_Lake_PackageSet_empty___closed__1, &l_Lake_PackageSet_empty___closed__1_once, _init_l_Lake_PackageSet_empty___closed__1);
return v___x_74_;
}
}
static lean_object* _init_l_Lake_OrdPackageSet_empty___closed__0(void){
_start:
{
lean_object* v___f_75_; lean_object* v___f_76_; lean_object* v___x_77_; 
v___f_75_ = ((lean_object*)(l_Lake_Package_instBEq___closed__0));
v___f_76_ = ((lean_object*)(l_Lake_Package_instHashable___closed__0));
v___x_77_ = l_Lake_OrdHashSet_empty(lean_box(0), v___f_76_, v___f_75_);
return v___x_77_;
}
}
static lean_object* _init_l_Lake_OrdPackageSet_empty(void){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_obj_once(&l_Lake_OrdPackageSet_empty___closed__0, &l_Lake_OrdPackageSet_empty___closed__0_once, _init_l_Lake_OrdPackageSet_empty___closed__0);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___lam__0(lean_object* v_self_79_){
_start:
{
lean_inc_ref(v_self_79_);
return v_self_79_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___lam__0___boxed(lean_object* v_self_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lake_NPackage_instCoeOutPackage___lam__0(v_self_80_);
lean_dec_ref(v_self_80_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage(lean_object* v_n_83_){
_start:
{
lean_object* v___f_84_; 
v___f_84_ = ((lean_object*)(l_Lake_NPackage_instCoeOutPackage___closed__0));
return v___f_84_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___boxed(lean_object* v_n_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lake_NPackage_instCoeOutPackage(v_n_85_);
lean_dec(v_n_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeDepPackageKeyName(lean_object* v_pkg_87_){
_start:
{
lean_inc_ref(v_pkg_87_);
return v_pkg_87_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeDepPackageKeyName___boxed(lean_object* v_pkg_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lake_NPackage_instCoeDepPackageKeyName(v_pkg_88_);
lean_dec_ref(v_pkg_88_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___lam__0(lean_object* v_x_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_box(0);
v___x_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v___y_92_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___lam__0___boxed(lean_object* v_x_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lake_instInhabitedPostUpdateHook_default___lam__0(v_x_96_, v___y_97_, v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v_x_96_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default(lean_object* v_a_102_){
_start:
{
lean_object* v___f_103_; 
v___f_103_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___closed__0));
return v___f_103_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___boxed(lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lake_instInhabitedPostUpdateHook_default(v_a_104_);
lean_dec(v_a_104_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook(lean_object* v_a_106_){
_start:
{
lean_object* v___f_107_; 
v___f_107_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___closed__0));
return v___f_107_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___boxed(lean_object* v_a_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lake_instInhabitedPostUpdateHook(v_a_108_);
lean_dec(v_a_108_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(lean_object* v_a_110_){
_start:
{
lean_inc_ref(v_a_110_);
return v_a_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg___boxed(lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(v_a_111_);
lean_dec_ref(v_a_111_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(lean_object* v_name_113_, lean_object* v_a_114_){
_start:
{
lean_inc_ref(v_a_114_);
return v_a_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed(lean_object* v_name_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(v_name_115_, v_a_116_);
lean_dec_ref(v_a_116_);
lean_dec(v_name_115_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeMk(lean_object* v_name_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_alloc_closure((void*)(l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed), 2, 1);
lean_closure_set(v___x_119_, 0, v_name_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(lean_object* v_a_120_){
_start:
{
lean_inc(v_a_120_);
return v_a_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg___boxed(lean_object* v_a_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(v_a_121_);
lean_dec(v_a_121_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(lean_object* v_name_123_, lean_object* v_a_124_){
_start:
{
lean_inc(v_a_124_);
return v_a_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed(lean_object* v_name_125_, lean_object* v_a_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(v_name_125_, v_a_126_);
lean_dec(v_a_126_);
lean_dec(v_name_125_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeGet(lean_object* v_name_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_alloc_closure((void*)(l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed), 2, 1);
lean_closure_set(v___x_129_, 0, v_name_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(lean_object* v_inst_130_){
_start:
{
lean_inc_ref(v_inst_130_);
return v_inst_130_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg___boxed(lean_object* v_inst_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(v_inst_131_);
lean_dec_ref(v_inst_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(lean_object* v_name_133_, lean_object* v_inst_134_){
_start:
{
lean_inc_ref(v_inst_134_);
return v_inst_134_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___boxed(lean_object* v_name_135_, lean_object* v_inst_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(v_name_135_, v_inst_136_);
lean_dec_ref(v_inst_136_);
lean_dec(v_name_135_);
return v_res_137_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isRoot(lean_object* v_self_145_){
_start:
{
lean_object* v_wsIdx_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v_wsIdx_146_ = lean_ctor_get(v_self_145_, 0);
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = lean_nat_dec_eq(v_wsIdx_146_, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isRoot___boxed(lean_object* v_self_149_){
_start:
{
uint8_t v_res_150_; lean_object* v_r_151_; 
v_res_150_ = l_Lake_Package_isRoot(v_self_149_);
lean_dec_ref(v_self_149_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_bootstrap(lean_object* v_self_152_){
_start:
{
lean_object* v_config_153_; uint8_t v_bootstrap_154_; 
v_config_153_ = lean_ctor_get(v_self_152_, 6);
v_bootstrap_154_ = lean_ctor_get_uint8(v_config_153_, sizeof(void*)*27);
return v_bootstrap_154_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_bootstrap___boxed(lean_object* v_self_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = l_Lake_Package_bootstrap(v_self_155_);
lean_dec_ref(v_self_155_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_id_x3f(lean_object* v_self_158_){
_start:
{
lean_object* v_config_159_; uint8_t v_bootstrap_160_; 
v_config_159_ = lean_ctor_get(v_self_158_, 6);
v_bootstrap_160_ = lean_ctor_get_uint8(v_config_159_, sizeof(void*)*27);
if (v_bootstrap_160_ == 0)
{
lean_object* v_origName_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_origName_161_ = lean_ctor_get(v_self_158_, 3);
lean_inc(v_origName_161_);
lean_dec_ref(v_self_158_);
v___x_162_ = l_Lean_Name_toString(v_origName_161_, v_bootstrap_160_);
v___x_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
else
{
lean_object* v___x_164_; 
lean_dec_ref(v_self_158_);
v___x_164_ = lean_box(0);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_version(lean_object* v_self_165_){
_start:
{
lean_object* v_config_166_; lean_object* v_version_167_; 
v_config_166_ = lean_ctor_get(v_self_165_, 6);
v_version_167_ = lean_ctor_get(v_config_166_, 17);
lean_inc_ref(v_version_167_);
return v_version_167_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_version___boxed(lean_object* v_self_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lake_Package_version(v_self_168_);
lean_dec_ref(v_self_168_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_versionTags(lean_object* v_self_170_){
_start:
{
lean_object* v_config_171_; lean_object* v_versionTags_172_; 
v_config_171_ = lean_ctor_get(v_self_170_, 6);
v_versionTags_172_ = lean_ctor_get(v_config_171_, 18);
lean_inc_ref(v_versionTags_172_);
return v_versionTags_172_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_versionTags___boxed(lean_object* v_self_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lake_Package_versionTags(v_self_173_);
lean_dec_ref(v_self_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_description(lean_object* v_self_175_){
_start:
{
lean_object* v_config_176_; lean_object* v_description_177_; 
v_config_176_ = lean_ctor_get(v_self_175_, 6);
v_description_177_ = lean_ctor_get(v_config_176_, 19);
lean_inc_ref(v_description_177_);
return v_description_177_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_description___boxed(lean_object* v_self_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lake_Package_description(v_self_178_);
lean_dec_ref(v_self_178_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_keywords(lean_object* v_self_180_){
_start:
{
lean_object* v_config_181_; lean_object* v_keywords_182_; 
v_config_181_ = lean_ctor_get(v_self_180_, 6);
v_keywords_182_ = lean_ctor_get(v_config_181_, 20);
lean_inc_ref(v_keywords_182_);
return v_keywords_182_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_keywords___boxed(lean_object* v_self_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lake_Package_keywords(v_self_183_);
lean_dec_ref(v_self_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_homepage(lean_object* v_self_185_){
_start:
{
lean_object* v_config_186_; lean_object* v_homepage_187_; 
v_config_186_ = lean_ctor_get(v_self_185_, 6);
v_homepage_187_ = lean_ctor_get(v_config_186_, 21);
lean_inc_ref(v_homepage_187_);
return v_homepage_187_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_homepage___boxed(lean_object* v_self_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lake_Package_homepage(v_self_188_);
lean_dec_ref(v_self_188_);
return v_res_189_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_reservoir(lean_object* v_self_190_){
_start:
{
lean_object* v_config_191_; uint8_t v_reservoir_192_; 
v_config_191_ = lean_ctor_get(v_self_190_, 6);
v_reservoir_192_ = lean_ctor_get_uint8(v_config_191_, sizeof(void*)*27 + 3);
return v_reservoir_192_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoir___boxed(lean_object* v_self_193_){
_start:
{
uint8_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = l_Lake_Package_reservoir(v_self_193_);
lean_dec_ref(v_self_193_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_license(lean_object* v_self_196_){
_start:
{
lean_object* v_config_197_; lean_object* v_license_198_; 
v_config_197_ = lean_ctor_get(v_self_196_, 6);
v_license_198_ = lean_ctor_get(v_config_197_, 22);
lean_inc_ref(v_license_198_);
return v_license_198_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_license___boxed(lean_object* v_self_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lake_Package_license(v_self_199_);
lean_dec_ref(v_self_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLicenseFiles(lean_object* v_self_221_){
_start:
{
lean_object* v_config_222_; lean_object* v_licenseFiles_223_; lean_object* v___f_224_; lean_object* v___x_225_; size_t v_sz_226_; size_t v___x_227_; lean_object* v___x_228_; 
v_config_222_ = lean_ctor_get(v_self_221_, 6);
lean_inc_ref(v_config_222_);
lean_dec_ref(v_self_221_);
v_licenseFiles_223_ = lean_ctor_get(v_config_222_, 23);
lean_inc_ref(v_licenseFiles_223_);
lean_dec_ref(v_config_222_);
v___f_224_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__0));
v___x_225_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__10));
v_sz_226_ = lean_array_size(v_licenseFiles_223_);
v___x_227_ = ((size_t)0ULL);
v___x_228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_225_, v___f_224_, v_sz_226_, v___x_227_, v_licenseFiles_223_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles___lam__0(lean_object* v_dir_229_, lean_object* v_x_230_){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = l_System_FilePath_normalize(v_x_230_);
v___x_232_ = l_Lake_joinRelative(v_dir_229_, v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles(lean_object* v_self_233_){
_start:
{
lean_object* v_config_234_; lean_object* v_dir_235_; lean_object* v_licenseFiles_236_; lean_object* v___f_237_; lean_object* v___f_238_; lean_object* v___x_239_; size_t v_sz_240_; size_t v___x_241_; lean_object* v___x_242_; size_t v_sz_243_; lean_object* v___x_244_; 
v_config_234_ = lean_ctor_get(v_self_233_, 6);
lean_inc_ref(v_config_234_);
v_dir_235_ = lean_ctor_get(v_self_233_, 4);
lean_inc_ref(v_dir_235_);
lean_dec_ref(v_self_233_);
v_licenseFiles_236_ = lean_ctor_get(v_config_234_, 23);
lean_inc_ref(v_licenseFiles_236_);
lean_dec_ref(v_config_234_);
v___f_237_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__0));
v___f_238_ = lean_alloc_closure((void*)(l_Lake_Package_licenseFiles___lam__0), 2, 1);
lean_closure_set(v___f_238_, 0, v_dir_235_);
v___x_239_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__10));
v_sz_240_ = lean_array_size(v_licenseFiles_236_);
v___x_241_ = ((size_t)0ULL);
v___x_242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_239_, v___f_237_, v_sz_240_, v___x_241_, v_licenseFiles_236_);
v_sz_243_ = lean_array_size(v___x_242_);
v___x_244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_239_, v___f_238_, v_sz_243_, v___x_241_, v___x_242_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relReadmeFile(lean_object* v_self_245_){
_start:
{
lean_object* v_config_246_; lean_object* v_readmeFile_247_; lean_object* v___x_248_; 
v_config_246_ = lean_ctor_get(v_self_245_, 6);
lean_inc_ref(v_config_246_);
lean_dec_ref(v_self_245_);
v_readmeFile_247_ = lean_ctor_get(v_config_246_, 24);
lean_inc_ref(v_readmeFile_247_);
lean_dec_ref(v_config_246_);
v___x_248_ = l_System_FilePath_normalize(v_readmeFile_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_readmeFile(lean_object* v_self_249_){
_start:
{
lean_object* v_config_250_; lean_object* v_dir_251_; lean_object* v_readmeFile_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_config_250_ = lean_ctor_get(v_self_249_, 6);
lean_inc_ref(v_config_250_);
v_dir_251_ = lean_ctor_get(v_self_249_, 4);
lean_inc_ref(v_dir_251_);
lean_dec_ref(v_self_249_);
v_readmeFile_252_ = lean_ctor_get(v_config_250_, 24);
lean_inc_ref(v_readmeFile_252_);
lean_dec_ref(v_config_250_);
v___x_253_ = l_System_FilePath_normalize(v_readmeFile_252_);
v___x_254_ = l_Lake_joinRelative(v_dir_251_, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir(lean_object* v_x_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lake_defaultLakeDir;
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___boxed(lean_object* v_x_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lake_Package_relLakeDir(v_x_257_);
lean_dec_ref(v_x_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lakeDir(lean_object* v_self_259_){
_start:
{
lean_object* v_dir_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_dir_260_ = lean_ctor_get(v_self_259_, 4);
lean_inc_ref(v_dir_260_);
lean_dec_ref(v_self_259_);
v___x_261_ = l_Lake_defaultLakeDir;
v___x_262_ = l_Lake_joinRelative(v_dir_260_, v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relPkgsDir(lean_object* v_self_263_){
_start:
{
lean_object* v_config_264_; lean_object* v_toWorkspaceConfig_265_; lean_object* v___x_266_; 
v_config_264_ = lean_ctor_get(v_self_263_, 6);
lean_inc_ref(v_config_264_);
lean_dec_ref(v_self_263_);
v_toWorkspaceConfig_265_ = lean_ctor_get(v_config_264_, 0);
lean_inc_ref(v_toWorkspaceConfig_265_);
lean_dec_ref(v_config_264_);
v___x_266_ = l_System_FilePath_normalize(v_toWorkspaceConfig_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_pkgsDir(lean_object* v_self_267_){
_start:
{
lean_object* v_config_268_; lean_object* v_dir_269_; lean_object* v_toWorkspaceConfig_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_config_268_ = lean_ctor_get(v_self_267_, 6);
lean_inc_ref(v_config_268_);
v_dir_269_ = lean_ctor_get(v_self_267_, 4);
lean_inc_ref(v_dir_269_);
lean_dec_ref(v_self_267_);
v_toWorkspaceConfig_270_ = lean_ctor_get(v_config_268_, 0);
lean_inc_ref(v_toWorkspaceConfig_270_);
lean_dec_ref(v_config_268_);
v___x_271_ = l_System_FilePath_normalize(v_toWorkspaceConfig_270_);
v___x_272_ = l_Lake_joinRelative(v_dir_269_, v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_manifestFile(lean_object* v_self_273_){
_start:
{
lean_object* v_dir_274_; lean_object* v_relManifestFile_275_; lean_object* v___x_276_; 
v_dir_274_ = lean_ctor_get(v_self_273_, 4);
lean_inc_ref(v_dir_274_);
v_relManifestFile_275_ = lean_ctor_get(v_self_273_, 9);
lean_inc_ref(v_relManifestFile_275_);
lean_dec_ref(v_self_273_);
v___x_276_ = l_Lake_joinRelative(v_dir_274_, v_relManifestFile_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildDir(lean_object* v_self_277_){
_start:
{
lean_object* v_config_278_; lean_object* v_dir_279_; lean_object* v_buildDir_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_config_278_ = lean_ctor_get(v_self_277_, 6);
lean_inc_ref(v_config_278_);
v_dir_279_ = lean_ctor_get(v_self_277_, 4);
lean_inc_ref(v_dir_279_);
lean_dec_ref(v_self_277_);
v_buildDir_280_ = lean_ctor_get(v_config_278_, 6);
lean_inc_ref(v_buildDir_280_);
lean_dec_ref(v_config_278_);
v___x_281_ = l_System_FilePath_normalize(v_buildDir_280_);
v___x_282_ = l_Lake_joinRelative(v_dir_279_, v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs(lean_object* v_self_283_){
_start:
{
lean_object* v_config_284_; lean_object* v_testDriverArgs_285_; 
v_config_284_ = lean_ctor_get(v_self_283_, 6);
v_testDriverArgs_285_ = lean_ctor_get(v_config_284_, 14);
lean_inc_ref(v_testDriverArgs_285_);
return v_testDriverArgs_285_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs___boxed(lean_object* v_self_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lake_Package_testDriverArgs(v_self_286_);
lean_dec_ref(v_self_286_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs(lean_object* v_self_288_){
_start:
{
lean_object* v_config_289_; lean_object* v_lintDriverArgs_290_; 
v_config_289_ = lean_ctor_get(v_self_288_, 6);
v_lintDriverArgs_290_ = lean_ctor_get(v_config_289_, 16);
lean_inc_ref(v_lintDriverArgs_290_);
return v_lintDriverArgs_290_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs___boxed(lean_object* v_self_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lake_Package_lintDriverArgs(v_self_291_);
lean_dec_ref(v_self_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets(lean_object* v_self_293_){
_start:
{
lean_object* v_config_294_; lean_object* v_extraDepTargets_295_; 
v_config_294_ = lean_ctor_get(v_self_293_, 6);
v_extraDepTargets_295_ = lean_ctor_get(v_config_294_, 3);
lean_inc_ref(v_extraDepTargets_295_);
return v_extraDepTargets_295_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets___boxed(lean_object* v_self_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lake_Package_extraDepTargets(v_self_296_);
lean_dec_ref(v_self_296_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent(lean_object* v_self_298_){
_start:
{
lean_object* v_config_299_; lean_object* v_toLeanConfig_300_; lean_object* v_platformIndependent_301_; 
v_config_299_ = lean_ctor_get(v_self_298_, 6);
v_toLeanConfig_300_ = lean_ctor_get(v_config_299_, 1);
v_platformIndependent_301_ = lean_ctor_get(v_toLeanConfig_300_, 10);
lean_inc(v_platformIndependent_301_);
return v_platformIndependent_301_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent___boxed(lean_object* v_self_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lake_Package_platformIndependent(v_self_302_);
lean_dec_ref(v_self_302_);
return v_res_303_;
}
}
static lean_object* _init_l_Lake_Package_isPlatformIndependent___closed__0(void){
_start:
{
lean_object* v___x_304_; lean_object* v___f_305_; 
v___x_304_ = lean_alloc_closure((void*)(l_instDecidableEqBool___boxed), 2, 0);
v___f_305_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_305_, 0, v___x_304_);
return v___f_305_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isPlatformIndependent(lean_object* v_self_309_){
_start:
{
lean_object* v_config_310_; lean_object* v_toLeanConfig_311_; lean_object* v_platformIndependent_312_; lean_object* v___f_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v_config_310_ = lean_ctor_get(v_self_309_, 6);
lean_inc_ref(v_config_310_);
lean_dec_ref(v_self_309_);
v_toLeanConfig_311_ = lean_ctor_get(v_config_310_, 1);
lean_inc_ref(v_toLeanConfig_311_);
lean_dec_ref(v_config_310_);
v_platformIndependent_312_ = lean_ctor_get(v_toLeanConfig_311_, 10);
lean_inc(v_platformIndependent_312_);
lean_dec_ref(v_toLeanConfig_311_);
v___f_313_ = lean_obj_once(&l_Lake_Package_isPlatformIndependent___closed__0, &l_Lake_Package_isPlatformIndependent___closed__0_once, _init_l_Lake_Package_isPlatformIndependent___closed__0);
v___x_314_ = ((lean_object*)(l_Lake_Package_isPlatformIndependent___closed__1));
v___x_315_ = l_Option_instBEq_beq___redArg(v___f_313_, v_platformIndependent_312_, v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isPlatformIndependent___boxed(lean_object* v_self_316_){
_start:
{
uint8_t v_res_317_; lean_object* v_r_318_; 
v_res_317_ = l_Lake_Package_isPlatformIndependent(v_self_316_);
v_r_318_ = lean_box(v_res_317_);
return v_r_318_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f(lean_object* v_self_319_){
_start:
{
lean_object* v_config_320_; lean_object* v_releaseRepo_321_; 
v_config_320_ = lean_ctor_get(v_self_319_, 6);
v_releaseRepo_321_ = lean_ctor_get(v_config_320_, 11);
lean_inc(v_releaseRepo_321_);
return v_releaseRepo_321_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f___boxed(lean_object* v_self_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lake_Package_releaseRepo_x3f(v_self_322_);
lean_dec_ref(v_self_322_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f(lean_object* v_self_324_){
_start:
{
lean_object* v_remoteUrl_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v_remoteUrl_325_ = lean_ctor_get(v_self_324_, 11);
v___x_326_ = lean_string_utf8_byte_size(v_remoteUrl_325_);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_nat_dec_eq(v___x_326_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; 
v___x_329_ = lean_box(0);
return v___x_329_;
}
else
{
lean_object* v___x_330_; 
lean_inc_ref(v_remoteUrl_325_);
v___x_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_330_, 0, v_remoteUrl_325_);
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f___boxed(lean_object* v_self_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lake_Package_remoteUrl_x3f(v_self_331_);
lean_dec_ref(v_self_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildArchiveFile(lean_object* v_self_333_){
_start:
{
lean_object* v_dir_334_; lean_object* v_buildArchive_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_dir_334_ = lean_ctor_get(v_self_333_, 4);
lean_inc_ref(v_dir_334_);
v_buildArchive_335_ = lean_ctor_get(v_self_333_, 19);
lean_inc_ref(v_buildArchive_335_);
lean_dec_ref(v_self_333_);
v___x_336_ = l_Lake_defaultLakeDir;
v___x_337_ = l_Lake_joinRelative(v_dir_334_, v___x_336_);
v___x_338_ = l_Lake_joinRelative(v___x_337_, v_buildArchive_335_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFile(lean_object* v_self_340_){
_start:
{
lean_object* v_dir_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_dir_341_ = lean_ctor_get(v_self_340_, 4);
lean_inc_ref(v_dir_341_);
lean_dec_ref(v_self_340_);
v___x_342_ = l_Lake_defaultLakeDir;
v___x_343_ = l_Lake_joinRelative(v_dir_341_, v___x_342_);
v___x_344_ = ((lean_object*)(l_Lake_Package_barrelFile___closed__0));
v___x_345_ = l_Lake_joinRelative(v___x_343_, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_preferReleaseBuild(lean_object* v_self_346_){
_start:
{
lean_object* v_config_347_; uint8_t v_preferReleaseBuild_348_; 
v_config_347_ = lean_ctor_get(v_self_346_, 6);
v_preferReleaseBuild_348_ = lean_ctor_get_uint8(v_config_347_, sizeof(void*)*27 + 2);
return v_preferReleaseBuild_348_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_preferReleaseBuild___boxed(lean_object* v_self_349_){
_start:
{
uint8_t v_res_350_; lean_object* v_r_351_; 
v_res_350_ = l_Lake_Package_preferReleaseBuild(v_self_349_);
lean_dec_ref(v_self_349_);
v_r_351_ = lean_box(v_res_350_);
return v_r_351_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_precompileModules(lean_object* v_self_352_){
_start:
{
lean_object* v_config_353_; uint8_t v_precompileModules_354_; 
v_config_353_ = lean_ctor_get(v_self_352_, 6);
v_precompileModules_354_ = lean_ctor_get_uint8(v_config_353_, sizeof(void*)*27 + 1);
return v_precompileModules_354_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_precompileModules___boxed(lean_object* v_self_355_){
_start:
{
uint8_t v_res_356_; lean_object* v_r_357_; 
v_res_356_ = l_Lake_Package_precompileModules(v_self_355_);
lean_dec_ref(v_self_355_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs(lean_object* v_self_358_){
_start:
{
lean_object* v_config_359_; lean_object* v_moreGlobalServerArgs_360_; 
v_config_359_ = lean_ctor_get(v_self_358_, 6);
v_moreGlobalServerArgs_360_ = lean_ctor_get(v_config_359_, 4);
lean_inc_ref(v_moreGlobalServerArgs_360_);
return v_moreGlobalServerArgs_360_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs___boxed(lean_object* v_self_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lake_Package_moreGlobalServerArgs(v_self_361_);
lean_dec_ref(v_self_361_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions(lean_object* v_self_363_){
_start:
{
lean_object* v_config_364_; lean_object* v_toLeanConfig_365_; lean_object* v_leanOptions_366_; lean_object* v_moreServerOptions_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v_config_364_ = lean_ctor_get(v_self_363_, 6);
v_toLeanConfig_365_ = lean_ctor_get(v_config_364_, 1);
v_leanOptions_366_ = lean_ctor_get(v_toLeanConfig_365_, 0);
v_moreServerOptions_367_ = lean_ctor_get(v_toLeanConfig_365_, 4);
v___x_368_ = l_Lean_LeanOptions_ofArray(v_leanOptions_366_);
v___x_369_ = l_Lean_LeanOptions_appendArray(v___x_368_, v_moreServerOptions_367_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions___boxed(lean_object* v_self_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lake_Package_moreServerOptions(v_self_370_);
lean_dec_ref(v_self_370_);
return v_res_371_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_buildType(lean_object* v_self_372_){
_start:
{
lean_object* v_config_373_; lean_object* v_toLeanConfig_374_; uint8_t v_buildType_375_; 
v_config_373_ = lean_ctor_get(v_self_372_, 6);
v_toLeanConfig_374_ = lean_ctor_get(v_config_373_, 1);
v_buildType_375_ = lean_ctor_get_uint8(v_toLeanConfig_374_, sizeof(void*)*13);
return v_buildType_375_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildType___boxed(lean_object* v_self_376_){
_start:
{
uint8_t v_res_377_; lean_object* v_r_378_; 
v_res_377_ = l_Lake_Package_buildType(v_self_376_);
lean_dec_ref(v_self_376_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_backend(lean_object* v_self_379_){
_start:
{
lean_object* v_config_380_; lean_object* v_toLeanConfig_381_; uint8_t v_backend_382_; 
v_config_380_ = lean_ctor_get(v_self_379_, 6);
v_toLeanConfig_381_ = lean_ctor_get(v_config_380_, 1);
v_backend_382_ = lean_ctor_get_uint8(v_toLeanConfig_381_, sizeof(void*)*13 + 1);
return v_backend_382_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_backend___boxed(lean_object* v_self_383_){
_start:
{
uint8_t v_res_384_; lean_object* v_r_385_; 
v_res_384_ = l_Lake_Package_backend(v_self_383_);
lean_dec_ref(v_self_383_);
v_r_385_ = lean_box(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_allowImportAll(lean_object* v_self_386_){
_start:
{
lean_object* v_config_387_; uint8_t v_allowImportAll_388_; 
v_config_387_ = lean_ctor_get(v_self_386_, 6);
v_allowImportAll_388_ = lean_ctor_get_uint8(v_config_387_, sizeof(void*)*27 + 5);
return v_allowImportAll_388_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_allowImportAll___boxed(lean_object* v_self_389_){
_start:
{
uint8_t v_res_390_; lean_object* v_r_391_; 
v_res_390_ = l_Lake_Package_allowImportAll(v_self_389_);
lean_dec_ref(v_self_389_);
v_r_391_ = lean_box(v_res_390_);
return v_r_391_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs(lean_object* v_self_392_){
_start:
{
lean_object* v_config_393_; lean_object* v_toLeanConfig_394_; lean_object* v_dynlibs_395_; 
v_config_393_ = lean_ctor_get(v_self_392_, 6);
v_toLeanConfig_394_ = lean_ctor_get(v_config_393_, 1);
v_dynlibs_395_ = lean_ctor_get(v_toLeanConfig_394_, 11);
lean_inc_ref(v_dynlibs_395_);
return v_dynlibs_395_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs___boxed(lean_object* v_self_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lake_Package_dynlibs(v_self_396_);
lean_dec_ref(v_self_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins(lean_object* v_self_398_){
_start:
{
lean_object* v_config_399_; lean_object* v_toLeanConfig_400_; lean_object* v_plugins_401_; 
v_config_399_ = lean_ctor_get(v_self_398_, 6);
v_toLeanConfig_400_ = lean_ctor_get(v_config_399_, 1);
v_plugins_401_ = lean_ctor_get(v_toLeanConfig_400_, 12);
lean_inc_ref(v_plugins_401_);
return v_plugins_401_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins___boxed(lean_object* v_self_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lake_Package_plugins(v_self_402_);
lean_dec_ref(v_self_402_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions(lean_object* v_self_404_){
_start:
{
lean_object* v_config_405_; lean_object* v_toLeanConfig_406_; lean_object* v_leanOptions_407_; lean_object* v___x_408_; 
v_config_405_ = lean_ctor_get(v_self_404_, 6);
v_toLeanConfig_406_ = lean_ctor_get(v_config_405_, 1);
v_leanOptions_407_ = lean_ctor_get(v_toLeanConfig_406_, 0);
v___x_408_ = l_Lean_LeanOptions_ofArray(v_leanOptions_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions___boxed(lean_object* v_self_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lake_Package_leanOptions(v_self_409_);
lean_dec_ref(v_self_409_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs(lean_object* v_self_411_){
_start:
{
lean_object* v_config_412_; lean_object* v_toLeanConfig_413_; lean_object* v_moreLeanArgs_414_; 
v_config_412_ = lean_ctor_get(v_self_411_, 6);
v_toLeanConfig_413_ = lean_ctor_get(v_config_412_, 1);
v_moreLeanArgs_414_ = lean_ctor_get(v_toLeanConfig_413_, 1);
lean_inc_ref(v_moreLeanArgs_414_);
return v_moreLeanArgs_414_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs___boxed(lean_object* v_self_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lake_Package_moreLeanArgs(v_self_415_);
lean_dec_ref(v_self_415_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs(lean_object* v_self_417_){
_start:
{
lean_object* v_config_418_; lean_object* v_toLeanConfig_419_; lean_object* v_weakLeanArgs_420_; 
v_config_418_ = lean_ctor_get(v_self_417_, 6);
v_toLeanConfig_419_ = lean_ctor_get(v_config_418_, 1);
v_weakLeanArgs_420_ = lean_ctor_get(v_toLeanConfig_419_, 2);
lean_inc_ref(v_weakLeanArgs_420_);
return v_weakLeanArgs_420_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs___boxed(lean_object* v_self_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lake_Package_weakLeanArgs(v_self_421_);
lean_dec_ref(v_self_421_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs(lean_object* v_self_423_){
_start:
{
lean_object* v_config_424_; lean_object* v_toLeanConfig_425_; lean_object* v_moreLeancArgs_426_; 
v_config_424_ = lean_ctor_get(v_self_423_, 6);
v_toLeanConfig_425_ = lean_ctor_get(v_config_424_, 1);
v_moreLeancArgs_426_ = lean_ctor_get(v_toLeanConfig_425_, 3);
lean_inc_ref(v_moreLeancArgs_426_);
return v_moreLeancArgs_426_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs___boxed(lean_object* v_self_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lake_Package_moreLeancArgs(v_self_427_);
lean_dec_ref(v_self_427_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs(lean_object* v_self_429_){
_start:
{
lean_object* v_config_430_; lean_object* v_toLeanConfig_431_; lean_object* v_weakLeancArgs_432_; 
v_config_430_ = lean_ctor_get(v_self_429_, 6);
v_toLeanConfig_431_ = lean_ctor_get(v_config_430_, 1);
v_weakLeancArgs_432_ = lean_ctor_get(v_toLeanConfig_431_, 5);
lean_inc_ref(v_weakLeancArgs_432_);
return v_weakLeancArgs_432_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs___boxed(lean_object* v_self_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lake_Package_weakLeancArgs(v_self_433_);
lean_dec_ref(v_self_433_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs(lean_object* v_self_435_){
_start:
{
lean_object* v_config_436_; lean_object* v_toLeanConfig_437_; lean_object* v_moreLinkObjs_438_; 
v_config_436_ = lean_ctor_get(v_self_435_, 6);
v_toLeanConfig_437_ = lean_ctor_get(v_config_436_, 1);
v_moreLinkObjs_438_ = lean_ctor_get(v_toLeanConfig_437_, 6);
lean_inc_ref(v_moreLinkObjs_438_);
return v_moreLinkObjs_438_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs___boxed(lean_object* v_self_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lake_Package_moreLinkObjs(v_self_439_);
lean_dec_ref(v_self_439_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs(lean_object* v_self_441_){
_start:
{
lean_object* v_config_442_; lean_object* v_toLeanConfig_443_; lean_object* v_moreLinkLibs_444_; 
v_config_442_ = lean_ctor_get(v_self_441_, 6);
v_toLeanConfig_443_ = lean_ctor_get(v_config_442_, 1);
v_moreLinkLibs_444_ = lean_ctor_get(v_toLeanConfig_443_, 7);
lean_inc_ref(v_moreLinkLibs_444_);
return v_moreLinkLibs_444_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs___boxed(lean_object* v_self_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lake_Package_moreLinkLibs(v_self_445_);
lean_dec_ref(v_self_445_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs(lean_object* v_self_447_){
_start:
{
lean_object* v_config_448_; lean_object* v_toLeanConfig_449_; lean_object* v_moreLinkArgs_450_; 
v_config_448_ = lean_ctor_get(v_self_447_, 6);
v_toLeanConfig_449_ = lean_ctor_get(v_config_448_, 1);
v_moreLinkArgs_450_ = lean_ctor_get(v_toLeanConfig_449_, 8);
lean_inc_ref(v_moreLinkArgs_450_);
return v_moreLinkArgs_450_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs___boxed(lean_object* v_self_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lake_Package_moreLinkArgs(v_self_451_);
lean_dec_ref(v_self_451_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs(lean_object* v_self_453_){
_start:
{
lean_object* v_config_454_; lean_object* v_toLeanConfig_455_; lean_object* v_weakLinkArgs_456_; 
v_config_454_ = lean_ctor_get(v_self_453_, 6);
v_toLeanConfig_455_ = lean_ctor_get(v_config_454_, 1);
v_weakLinkArgs_456_ = lean_ctor_get(v_toLeanConfig_455_, 9);
lean_inc_ref(v_weakLinkArgs_456_);
return v_weakLinkArgs_456_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs___boxed(lean_object* v_self_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lake_Package_weakLinkArgs(v_self_457_);
lean_dec_ref(v_self_457_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_srcDir(lean_object* v_self_459_){
_start:
{
lean_object* v_config_460_; lean_object* v_dir_461_; lean_object* v_srcDir_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_config_460_ = lean_ctor_get(v_self_459_, 6);
lean_inc_ref(v_config_460_);
v_dir_461_ = lean_ctor_get(v_self_459_, 4);
lean_inc_ref(v_dir_461_);
lean_dec_ref(v_self_459_);
v_srcDir_462_ = lean_ctor_get(v_config_460_, 5);
lean_inc_ref(v_srcDir_462_);
lean_dec_ref(v_config_460_);
v___x_463_ = l_System_FilePath_normalize(v_srcDir_462_);
v___x_464_ = l_Lake_joinRelative(v_dir_461_, v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_rootDir(lean_object* v_self_465_){
_start:
{
lean_object* v_config_466_; lean_object* v_dir_467_; lean_object* v_srcDir_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v_config_466_ = lean_ctor_get(v_self_465_, 6);
lean_inc_ref(v_config_466_);
v_dir_467_ = lean_ctor_get(v_self_465_, 4);
lean_inc_ref(v_dir_467_);
lean_dec_ref(v_self_465_);
v_srcDir_468_ = lean_ctor_get(v_config_466_, 5);
lean_inc_ref(v_srcDir_468_);
lean_dec_ref(v_config_466_);
v___x_469_ = l_System_FilePath_normalize(v_srcDir_468_);
v___x_470_ = l_Lake_joinRelative(v_dir_467_, v___x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanLibDir(lean_object* v_self_471_){
_start:
{
lean_object* v_config_472_; lean_object* v_dir_473_; lean_object* v_buildDir_474_; lean_object* v_leanLibDir_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_config_472_ = lean_ctor_get(v_self_471_, 6);
lean_inc_ref(v_config_472_);
v_dir_473_ = lean_ctor_get(v_self_471_, 4);
lean_inc_ref(v_dir_473_);
lean_dec_ref(v_self_471_);
v_buildDir_474_ = lean_ctor_get(v_config_472_, 6);
lean_inc_ref(v_buildDir_474_);
v_leanLibDir_475_ = lean_ctor_get(v_config_472_, 7);
lean_inc_ref(v_leanLibDir_475_);
lean_dec_ref(v_config_472_);
v___x_476_ = l_System_FilePath_normalize(v_buildDir_474_);
v___x_477_ = l_Lake_joinRelative(v_dir_473_, v___x_476_);
v___x_478_ = l_System_FilePath_normalize(v_leanLibDir_475_);
v___x_479_ = l_Lake_joinRelative(v___x_477_, v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_staticLibDir(lean_object* v_self_480_){
_start:
{
lean_object* v_config_481_; lean_object* v_dir_482_; lean_object* v_buildDir_483_; lean_object* v_nativeLibDir_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_config_481_ = lean_ctor_get(v_self_480_, 6);
lean_inc_ref(v_config_481_);
v_dir_482_ = lean_ctor_get(v_self_480_, 4);
lean_inc_ref(v_dir_482_);
lean_dec_ref(v_self_480_);
v_buildDir_483_ = lean_ctor_get(v_config_481_, 6);
lean_inc_ref(v_buildDir_483_);
v_nativeLibDir_484_ = lean_ctor_get(v_config_481_, 8);
lean_inc_ref(v_nativeLibDir_484_);
lean_dec_ref(v_config_481_);
v___x_485_ = l_System_FilePath_normalize(v_buildDir_483_);
v___x_486_ = l_Lake_joinRelative(v_dir_482_, v___x_485_);
v___x_487_ = l_System_FilePath_normalize(v_nativeLibDir_484_);
v___x_488_ = l_Lake_joinRelative(v___x_486_, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_sharedLibDir(lean_object* v_self_489_){
_start:
{
lean_object* v_config_490_; lean_object* v_dir_491_; lean_object* v_buildDir_492_; lean_object* v_nativeLibDir_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v_config_490_ = lean_ctor_get(v_self_489_, 6);
lean_inc_ref(v_config_490_);
v_dir_491_ = lean_ctor_get(v_self_489_, 4);
lean_inc_ref(v_dir_491_);
lean_dec_ref(v_self_489_);
v_buildDir_492_ = lean_ctor_get(v_config_490_, 6);
lean_inc_ref(v_buildDir_492_);
v_nativeLibDir_493_ = lean_ctor_get(v_config_490_, 8);
lean_inc_ref(v_nativeLibDir_493_);
lean_dec_ref(v_config_490_);
v___x_494_ = l_System_FilePath_normalize(v_buildDir_492_);
v___x_495_ = l_Lake_joinRelative(v_dir_491_, v___x_494_);
v___x_496_ = l_System_FilePath_normalize(v_nativeLibDir_493_);
v___x_497_ = l_Lake_joinRelative(v___x_495_, v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_binDir(lean_object* v_self_498_){
_start:
{
lean_object* v_config_499_; lean_object* v_dir_500_; lean_object* v_buildDir_501_; lean_object* v_binDir_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v_config_499_ = lean_ctor_get(v_self_498_, 6);
lean_inc_ref(v_config_499_);
v_dir_500_ = lean_ctor_get(v_self_498_, 4);
lean_inc_ref(v_dir_500_);
lean_dec_ref(v_self_498_);
v_buildDir_501_ = lean_ctor_get(v_config_499_, 6);
lean_inc_ref(v_buildDir_501_);
v_binDir_502_ = lean_ctor_get(v_config_499_, 9);
lean_inc_ref(v_binDir_502_);
lean_dec_ref(v_config_499_);
v___x_503_ = l_System_FilePath_normalize(v_buildDir_501_);
v___x_504_ = l_Lake_joinRelative(v_dir_500_, v___x_503_);
v___x_505_ = l_System_FilePath_normalize(v_binDir_502_);
v___x_506_ = l_Lake_joinRelative(v___x_504_, v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_irDir(lean_object* v_self_507_){
_start:
{
lean_object* v_config_508_; lean_object* v_dir_509_; lean_object* v_buildDir_510_; lean_object* v_irDir_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_config_508_ = lean_ctor_get(v_self_507_, 6);
lean_inc_ref(v_config_508_);
v_dir_509_ = lean_ctor_get(v_self_507_, 4);
lean_inc_ref(v_dir_509_);
lean_dec_ref(v_self_507_);
v_buildDir_510_ = lean_ctor_get(v_config_508_, 6);
lean_inc_ref(v_buildDir_510_);
v_irDir_511_ = lean_ctor_get(v_config_508_, 10);
lean_inc_ref(v_irDir_511_);
lean_dec_ref(v_config_508_);
v___x_512_ = l_System_FilePath_normalize(v_buildDir_510_);
v___x_513_ = l_Lake_joinRelative(v_dir_509_, v___x_512_);
v___x_514_ = l_System_FilePath_normalize(v_irDir_511_);
v___x_515_ = l_Lake_joinRelative(v___x_513_, v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_libPrefixOnWindows(lean_object* v_self_516_){
_start:
{
lean_object* v_config_517_; uint8_t v_libPrefixOnWindows_518_; 
v_config_517_ = lean_ctor_get(v_self_516_, 6);
v_libPrefixOnWindows_518_ = lean_ctor_get_uint8(v_config_517_, sizeof(void*)*27 + 4);
return v_libPrefixOnWindows_518_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_libPrefixOnWindows___boxed(lean_object* v_self_519_){
_start:
{
uint8_t v_res_520_; lean_object* v_r_521_; 
v_res_520_ = l_Lake_Package_libPrefixOnWindows(v_self_519_);
lean_dec_ref(v_self_519_);
v_r_521_ = lean_box(v_res_520_);
return v_r_521_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f(lean_object* v_self_522_){
_start:
{
lean_object* v_config_523_; lean_object* v_enableArtifactCache_x3f_524_; 
v_config_523_ = lean_ctor_get(v_self_522_, 6);
v_enableArtifactCache_x3f_524_ = lean_ctor_get(v_config_523_, 25);
lean_inc(v_enableArtifactCache_x3f_524_);
return v_enableArtifactCache_x3f_524_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f___boxed(lean_object* v_self_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lake_Package_enableArtifactCache_x3f(v_self_525_);
lean_dec_ref(v_self_525_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f(lean_object* v_self_527_){
_start:
{
lean_object* v_config_528_; lean_object* v_restoreAllArtifacts_x3f_529_; 
v_config_528_ = lean_ctor_get(v_self_527_, 6);
v_restoreAllArtifacts_x3f_529_ = lean_ctor_get(v_config_528_, 26);
lean_inc(v_restoreAllArtifacts_x3f_529_);
return v_restoreAllArtifacts_x3f_529_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f___boxed(lean_object* v_self_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lake_Package_restoreAllArtifacts_x3f(v_self_530_);
lean_dec_ref(v_self_530_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_cacheScope(lean_object* v_self_532_){
_start:
{
lean_object* v_baseName_533_; uint8_t v___x_534_; lean_object* v___x_535_; 
v_baseName_533_ = lean_ctor_get(v_self_532_, 1);
lean_inc(v_baseName_533_);
lean_dec_ref(v_self_532_);
v___x_534_ = 0;
v___x_535_ = l_Lean_Name_toString(v_baseName_533_, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(lean_object* v_self_537_){
_start:
{
lean_object* v_origName_538_; lean_object* v_scope_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v_origName_538_ = lean_ctor_get(v_self_537_, 3);
lean_inc(v_origName_538_);
v_scope_539_ = lean_ctor_get(v_self_537_, 10);
lean_inc_ref(v_scope_539_);
lean_dec_ref(v_self_537_);
v___x_540_ = ((lean_object*)(l___private_Lake_Config_Package_0__Lake_Package_reservoirScope___closed__0));
v___x_541_ = lean_string_append(v_scope_539_, v___x_540_);
v___x_542_ = 0;
v___x_543_ = l_Lean_Name_toString(v_origName_538_, v___x_542_);
v___x_544_ = lean_string_append(v___x_541_, v___x_543_);
lean_dec_ref(v___x_543_);
v___x_545_ = l_Lake_CacheServiceScope_ofString(v___x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirScope_x3f(lean_object* v_self_546_){
_start:
{
lean_object* v_scope_547_; lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v_scope_547_ = lean_ctor_get(v_self_546_, 10);
v___x_548_ = lean_string_utf8_byte_size(v_scope_547_);
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = lean_nat_dec_eq(v___x_548_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(v_self_546_);
v___x_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
return v___x_552_;
}
else
{
lean_object* v___x_553_; 
lean_dec_ref(v_self_546_);
v___x_553_ = lean_box(0);
return v___x_553_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(lean_object* v_t_554_, lean_object* v_k_555_){
_start:
{
if (lean_obj_tag(v_t_554_) == 0)
{
lean_object* v_k_556_; lean_object* v_v_557_; lean_object* v_l_558_; lean_object* v_r_559_; uint8_t v___x_560_; 
v_k_556_ = lean_ctor_get(v_t_554_, 1);
v_v_557_ = lean_ctor_get(v_t_554_, 2);
v_l_558_ = lean_ctor_get(v_t_554_, 3);
v_r_559_ = lean_ctor_get(v_t_554_, 4);
v___x_560_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_555_, v_k_556_);
switch(v___x_560_)
{
case 0:
{
v_t_554_ = v_l_558_;
goto _start;
}
case 1:
{
lean_object* v___x_562_; 
lean_inc(v_v_557_);
v___x_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_562_, 0, v_v_557_);
return v___x_562_;
}
default: 
{
v_t_554_ = v_r_559_;
goto _start;
}
}
}
else
{
lean_object* v___x_564_; 
v___x_564_ = lean_box(0);
return v___x_564_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg___boxed(lean_object* v_t_565_, lean_object* v_k_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_565_, v_k_566_);
lean_dec(v_k_566_);
lean_dec(v_t_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object* v_name_568_, lean_object* v_self_569_){
_start:
{
lean_object* v_targetDeclMap_570_; lean_object* v___x_571_; 
v_targetDeclMap_570_ = lean_ctor_get(v_self_569_, 14);
v___x_571_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_targetDeclMap_570_, v_name_568_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f___boxed(lean_object* v_name_572_, lean_object* v_self_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lake_Package_findTargetDecl_x3f(v_name_572_, v_self_573_);
lean_dec_ref(v_self_573_);
lean_dec(v_name_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(lean_object* v_00_u03b2_575_, lean_object* v_inst_576_, lean_object* v_t_577_, lean_object* v_k_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_577_, v_k_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___boxed(lean_object* v_00_u03b2_580_, lean_object* v_inst_581_, lean_object* v_t_582_, lean_object* v_k_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(v_00_u03b2_580_, v_inst_581_, v_t_582_, v_k_583_);
lean_dec(v_k_583_);
lean_dec(v_t_582_);
return v_res_584_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(lean_object* v_mod_588_, lean_object* v_as_589_, size_t v_i_590_, size_t v_stop_591_){
_start:
{
uint8_t v___x_592_; 
v___x_592_ = lean_usize_dec_eq(v_i_590_, v_stop_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; lean_object* v_kind_594_; lean_object* v_config_595_; uint8_t v___x_596_; uint8_t v___y_598_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_593_ = lean_array_uget_borrowed(v_as_589_, v_i_590_);
v_kind_594_ = lean_ctor_get(v___x_593_, 2);
v_config_595_ = lean_ctor_get(v___x_593_, 3);
v___x_596_ = 1;
v___x_602_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1));
v___x_603_ = lean_name_eq(v_kind_594_, v___x_602_);
if (v___x_603_ == 0)
{
v___y_598_ = v___x_592_;
goto v___jp_597_;
}
else
{
uint8_t v___x_604_; 
v___x_604_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_588_, v_config_595_);
v___y_598_ = v___x_604_;
goto v___jp_597_;
}
v___jp_597_:
{
if (v___y_598_ == 0)
{
size_t v___x_599_; size_t v___x_600_; 
v___x_599_ = ((size_t)1ULL);
v___x_600_ = lean_usize_add(v_i_590_, v___x_599_);
v_i_590_ = v___x_600_;
goto _start;
}
else
{
return v___x_596_;
}
}
}
else
{
uint8_t v___x_605_; 
v___x_605_ = 0;
return v___x_605_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___boxed(lean_object* v_mod_606_, lean_object* v_as_607_, lean_object* v_i_608_, lean_object* v_stop_609_){
_start:
{
size_t v_i_boxed_610_; size_t v_stop_boxed_611_; uint8_t v_res_612_; lean_object* v_r_613_; 
v_i_boxed_610_ = lean_unbox_usize(v_i_608_);
lean_dec(v_i_608_);
v_stop_boxed_611_ = lean_unbox_usize(v_stop_609_);
lean_dec(v_stop_609_);
v_res_612_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_606_, v_as_607_, v_i_boxed_610_, v_stop_boxed_611_);
lean_dec_ref(v_as_607_);
lean_dec(v_mod_606_);
v_r_613_ = lean_box(v_res_612_);
return v_r_613_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isLocalModule(lean_object* v_mod_614_, lean_object* v_self_615_){
_start:
{
lean_object* v_targetDecls_616_; lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v_targetDecls_616_ = lean_ctor_get(v_self_615_, 13);
v___x_617_ = lean_unsigned_to_nat(0u);
v___x_618_ = lean_array_get_size(v_targetDecls_616_);
v___x_619_ = lean_nat_dec_lt(v___x_617_, v___x_618_);
if (v___x_619_ == 0)
{
return v___x_619_;
}
else
{
if (v___x_619_ == 0)
{
return v___x_619_;
}
else
{
size_t v___x_620_; size_t v___x_621_; uint8_t v___x_622_; 
v___x_620_ = ((size_t)0ULL);
v___x_621_ = lean_usize_of_nat(v___x_618_);
v___x_622_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_614_, v_targetDecls_616_, v___x_620_, v___x_621_);
return v___x_622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isLocalModule___boxed(lean_object* v_mod_623_, lean_object* v_self_624_){
_start:
{
uint8_t v_res_625_; lean_object* v_r_626_; 
v_res_625_ = l_Lake_Package_isLocalModule(v_mod_623_, v_self_624_);
lean_dec_ref(v_self_624_);
lean_dec(v_mod_623_);
v_r_626_ = lean_box(v_res_625_);
return v_r_626_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(lean_object* v_mod_627_, lean_object* v_as_628_, size_t v_i_629_, size_t v_stop_630_){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = lean_usize_dec_eq(v_i_629_, v_stop_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v_kind_633_; lean_object* v_config_634_; uint8_t v___x_635_; uint8_t v___y_637_; lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_632_ = lean_array_uget_borrowed(v_as_628_, v_i_629_);
v_kind_633_ = lean_ctor_get(v___x_632_, 2);
v_config_634_ = lean_ctor_get(v___x_632_, 3);
v___x_635_ = 1;
v___x_648_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1));
v___x_649_ = lean_name_eq(v_kind_633_, v___x_648_);
if (v___x_649_ == 0)
{
goto v___jp_641_;
}
else
{
uint8_t v___x_650_; 
v___x_650_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_627_, v_config_634_);
if (v___x_650_ == 0)
{
goto v___jp_641_;
}
else
{
v___y_637_ = v___x_650_;
goto v___jp_636_;
}
}
v___jp_636_:
{
if (v___y_637_ == 0)
{
size_t v___x_638_; size_t v___x_639_; 
v___x_638_ = ((size_t)1ULL);
v___x_639_ = lean_usize_add(v_i_629_, v___x_638_);
v_i_629_ = v___x_639_;
goto _start;
}
else
{
return v___x_635_;
}
}
v___jp_641_:
{
lean_object* v_kind_642_; lean_object* v_config_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v_kind_642_ = lean_ctor_get(v___x_632_, 2);
v_config_643_ = lean_ctor_get(v___x_632_, 3);
v___x_644_ = l_Lake_LeanExe_keyword;
v___x_645_ = lean_name_eq(v_kind_642_, v___x_644_);
if (v___x_645_ == 0)
{
v___y_637_ = v___x_631_;
goto v___jp_636_;
}
else
{
lean_object* v_root_646_; uint8_t v___x_647_; 
v_root_646_ = lean_ctor_get(v_config_643_, 2);
v___x_647_ = lean_name_eq(v_root_646_, v_mod_627_);
v___y_637_ = v___x_647_;
goto v___jp_636_;
}
}
}
else
{
uint8_t v___x_651_; 
v___x_651_ = 0;
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0___boxed(lean_object* v_mod_652_, lean_object* v_as_653_, lean_object* v_i_654_, lean_object* v_stop_655_){
_start:
{
size_t v_i_boxed_656_; size_t v_stop_boxed_657_; uint8_t v_res_658_; lean_object* v_r_659_; 
v_i_boxed_656_ = lean_unbox_usize(v_i_654_);
lean_dec(v_i_654_);
v_stop_boxed_657_ = lean_unbox_usize(v_stop_655_);
lean_dec(v_stop_655_);
v_res_658_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_652_, v_as_653_, v_i_boxed_656_, v_stop_boxed_657_);
lean_dec_ref(v_as_653_);
lean_dec(v_mod_652_);
v_r_659_ = lean_box(v_res_658_);
return v_r_659_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isBuildableModule(lean_object* v_mod_660_, lean_object* v_self_661_){
_start:
{
lean_object* v_targetDecls_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v_targetDecls_662_ = lean_ctor_get(v_self_661_, 13);
v___x_663_ = lean_unsigned_to_nat(0u);
v___x_664_ = lean_array_get_size(v_targetDecls_662_);
v___x_665_ = lean_nat_dec_lt(v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
return v___x_665_;
}
else
{
if (v___x_665_ == 0)
{
return v___x_665_;
}
else
{
size_t v___x_666_; size_t v___x_667_; uint8_t v___x_668_; 
v___x_666_ = ((size_t)0ULL);
v___x_667_ = lean_usize_of_nat(v___x_664_);
v___x_668_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_660_, v_targetDecls_662_, v___x_666_, v___x_667_);
return v___x_668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isBuildableModule___boxed(lean_object* v_mod_669_, lean_object* v_self_670_){
_start:
{
uint8_t v_res_671_; lean_object* v_r_672_; 
v_res_671_ = l_Lake_Package_isBuildableModule(v_mod_669_, v_self_670_);
lean_dec_ref(v_self_670_);
lean_dec(v_mod_669_);
v_r_672_ = lean_box(v_res_671_);
return v_r_672_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_clean(lean_object* v_self_673_){
_start:
{
lean_object* v_config_675_; lean_object* v_dir_676_; lean_object* v_buildDir_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v_config_675_ = lean_ctor_get(v_self_673_, 6);
lean_inc_ref(v_config_675_);
v_dir_676_ = lean_ctor_get(v_self_673_, 4);
lean_inc_ref(v_dir_676_);
lean_dec_ref(v_self_673_);
v_buildDir_677_ = lean_ctor_get(v_config_675_, 6);
lean_inc_ref(v_buildDir_677_);
lean_dec_ref(v_config_675_);
v___x_678_ = l_System_FilePath_normalize(v_buildDir_677_);
v___x_679_ = l_Lake_joinRelative(v_dir_676_, v___x_678_);
v___x_680_ = l_Lake_removeDirAllIfExists(v___x_679_);
lean_dec_ref(v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_clean___boxed(lean_object* v_self_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lake_Package_clean(v_self_681_);
return v_res_683_;
}
}
lean_object* runtime_initialize_Lake_Config_Cache(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Script(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_ConfigDecl(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Dependency(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_PackageConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_FilePath(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_OrdHashSet(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Name(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_OpaqueType(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Config_Cache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Script(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_ConfigDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Dependency(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_PackageConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_OrdHashSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_OpaqueType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedPackage_default = _init_l_Lake_instInhabitedPackage_default();
lean_mark_persistent(l_Lake_instInhabitedPackage_default);
l_Lake_instInhabitedPackage = _init_l_Lake_instInhabitedPackage();
lean_mark_persistent(l_Lake_instInhabitedPackage);
l_Lake_PackageSet_empty = _init_l_Lake_PackageSet_empty();
lean_mark_persistent(l_Lake_PackageSet_empty);
l_Lake_OrdPackageSet_empty = _init_l_Lake_OrdPackageSet_empty();
lean_mark_persistent(l_Lake_OrdPackageSet_empty);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Util_OpaqueType(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_Package(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Util_OpaqueType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Cache(uint8_t builtin);
lean_object* initialize_Lake_Config_Script(uint8_t builtin);
lean_object* initialize_Lake_Config_ConfigDecl(uint8_t builtin);
lean_object* initialize_Lake_Config_Dependency(uint8_t builtin);
lean_object* initialize_Lake_Config_PackageConfig(uint8_t builtin);
lean_object* initialize_Lake_Util_FilePath(uint8_t builtin);
lean_object* initialize_Lake_Util_OrdHashSet(uint8_t builtin);
lean_object* initialize_Lake_Util_Name(uint8_t builtin);
lean_object* initialize_Lake_Util_OpaqueType(uint8_t builtin);
lean_object* initialize_Lake_Util_OpaqueType(uint8_t builtin);
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Package(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Cache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Script(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_ConfigDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Dependency(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_PackageConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_OrdHashSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_OpaqueType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_OpaqueType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Package(builtin);
}
#ifdef __cplusplus
}
#endif
