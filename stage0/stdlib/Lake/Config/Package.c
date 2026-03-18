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
LEAN_EXPORT uint8_t l_Lake_Package_fixedToolchain(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_fixedToolchain___boxed(lean_object*);
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
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_10_ = lean_box(1);
v___x_11_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__2));
v___x_12_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__1));
v___x_13_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__0, &l_Lake_instInhabitedPackage_default___closed__0_once, _init_l_Lake_instInhabitedPackage_default___closed__0);
v___x_14_ = l_System_instInhabitedFilePath_default;
v___x_15_ = lean_box(0);
v___x_16_ = lean_unsigned_to_nat(0u);
v___x_17_ = lean_alloc_ctor(0, 22, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v___x_15_);
lean_ctor_set(v___x_17_, 2, v___x_15_);
lean_ctor_set(v___x_17_, 3, v___x_15_);
lean_ctor_set(v___x_17_, 4, v___x_14_);
lean_ctor_set(v___x_17_, 5, v___x_14_);
lean_ctor_set(v___x_17_, 6, v___x_13_);
lean_ctor_set(v___x_17_, 7, v___x_14_);
lean_ctor_set(v___x_17_, 8, v___x_14_);
lean_ctor_set(v___x_17_, 9, v___x_14_);
lean_ctor_set(v___x_17_, 10, v___x_12_);
lean_ctor_set(v___x_17_, 11, v___x_12_);
lean_ctor_set(v___x_17_, 12, v___x_11_);
lean_ctor_set(v___x_17_, 13, v___x_11_);
lean_ctor_set(v___x_17_, 14, v___x_10_);
lean_ctor_set(v___x_17_, 15, v___x_11_);
lean_ctor_set(v___x_17_, 16, v___x_10_);
lean_ctor_set(v___x_17_, 17, v___x_11_);
lean_ctor_set(v___x_17_, 18, v___x_11_);
lean_ctor_set(v___x_17_, 19, v___x_12_);
lean_ctor_set(v___x_17_, 20, v___x_12_);
lean_ctor_set(v___x_17_, 21, v___x_12_);
return v___x_17_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default(void){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__3, &l_Lake_instInhabitedPackage_default___closed__3_once, _init_l_Lake_instInhabitedPackage_default___closed__3);
return v___x_18_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage(void){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lake_instInhabitedPackage_default;
return v___x_19_;
}
}
static uint64_t _init_l_Lake_Package_instHashable___lam__0___closed__0(void){
_start:
{
lean_object* v___x_20_; uint64_t v___x_21_; 
v___x_20_ = lean_unsigned_to_nat(1723u);
v___x_21_ = lean_uint64_of_nat(v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT uint64_t l_Lake_Package_instHashable___lam__0(lean_object* v_pkg_22_){
_start:
{
lean_object* v_keyName_23_; 
v_keyName_23_ = lean_ctor_get(v_pkg_22_, 2);
if (lean_obj_tag(v_keyName_23_) == 0)
{
uint64_t v___x_24_; 
v___x_24_ = lean_uint64_once(&l_Lake_Package_instHashable___lam__0___closed__0, &l_Lake_Package_instHashable___lam__0___closed__0_once, _init_l_Lake_Package_instHashable___lam__0___closed__0);
return v___x_24_;
}
else
{
uint64_t v_hash_25_; 
v_hash_25_ = lean_ctor_get_uint64(v_keyName_23_, sizeof(void*)*2);
return v_hash_25_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instHashable___lam__0___boxed(lean_object* v_pkg_26_){
_start:
{
uint64_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_Lake_Package_instHashable___lam__0(v_pkg_26_);
lean_dec_ref(v_pkg_26_);
v_r_28_ = lean_box_uint64(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_instBEq___lam__0(lean_object* v_p1_31_, lean_object* v_p2_32_){
_start:
{
lean_object* v_wsIdx_33_; lean_object* v_wsIdx_34_; uint8_t v___x_35_; 
v_wsIdx_33_ = lean_ctor_get(v_p1_31_, 0);
v_wsIdx_34_ = lean_ctor_get(v_p2_32_, 0);
v___x_35_ = lean_nat_dec_eq(v_wsIdx_33_, v_wsIdx_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instBEq___lam__0___boxed(lean_object* v_p1_36_, lean_object* v_p2_37_){
_start:
{
uint8_t v_res_38_; lean_object* v_r_39_; 
v_res_38_ = l_Lake_Package_instBEq___lam__0(v_p1_36_, v_p2_37_);
lean_dec_ref(v_p2_37_);
lean_dec_ref(v_p1_36_);
v_r_39_ = lean_box(v_res_38_);
return v_r_39_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_prettyName(lean_object* v_self_42_){
_start:
{
lean_object* v_baseName_43_; uint8_t v___x_44_; lean_object* v___x_45_; 
v_baseName_43_ = lean_ctor_get(v_self_42_, 1);
lean_inc(v_baseName_43_);
lean_dec_ref(v_self_42_);
v___x_44_ = 0;
v___x_45_ = l_Lean_Name_toString(v_baseName_43_, v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instQueryJson___lam__0(lean_object* v_x_46_){
_start:
{
lean_object* v_keyName_47_; uint8_t v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_keyName_47_ = lean_ctor_get(v_x_46_, 2);
lean_inc(v_keyName_47_);
lean_dec_ref(v_x_46_);
v___x_48_ = 1;
v___x_49_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_keyName_47_, v___x_48_);
v___x_50_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instQueryText___lam__0(lean_object* v_x_53_){
_start:
{
lean_object* v_baseName_54_; uint8_t v___x_55_; lean_object* v___x_56_; 
v_baseName_54_ = lean_ctor_get(v_x_53_, 1);
lean_inc(v_baseName_54_);
lean_dec_ref(v_x_53_);
v___x_55_ = 0;
v___x_56_ = l_Lean_Name_toString(v_baseName_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_name(lean_object* v_self_59_){
_start:
{
lean_object* v_baseName_60_; 
v_baseName_60_ = lean_ctor_get(v_self_59_, 1);
lean_inc(v_baseName_60_);
return v_baseName_60_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_name___boxed(lean_object* v_self_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lake_Package_name(v_self_61_);
lean_dec_ref(v_self_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirName(lean_object* v_self_63_){
_start:
{
lean_object* v_origName_64_; uint8_t v___x_65_; lean_object* v___x_66_; 
v_origName_64_ = lean_ctor_get(v_self_63_, 3);
lean_inc(v_origName_64_);
lean_dec_ref(v_self_63_);
v___x_65_ = 0;
v___x_66_ = l_Lean_Name_toString(v_origName_64_, v___x_65_);
return v___x_66_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty___closed__0(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_box(0);
v___x_68_ = lean_unsigned_to_nat(16u);
v___x_69_ = lean_mk_array(v___x_68_, v___x_67_);
return v___x_69_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty___closed__1(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = lean_obj_once(&l_Lake_PackageSet_empty___closed__0, &l_Lake_PackageSet_empty___closed__0_once, _init_l_Lake_PackageSet_empty___closed__0);
v___x_71_ = lean_unsigned_to_nat(0u);
v___x_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v___x_70_);
return v___x_72_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty(void){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_obj_once(&l_Lake_PackageSet_empty___closed__1, &l_Lake_PackageSet_empty___closed__1_once, _init_l_Lake_PackageSet_empty___closed__1);
return v___x_73_;
}
}
static lean_object* _init_l_Lake_OrdPackageSet_empty___closed__0(void){
_start:
{
lean_object* v___f_74_; lean_object* v___f_75_; lean_object* v___x_76_; 
v___f_74_ = ((lean_object*)(l_Lake_Package_instBEq___closed__0));
v___f_75_ = ((lean_object*)(l_Lake_Package_instHashable___closed__0));
v___x_76_ = l_Lake_OrdHashSet_empty(lean_box(0), v___f_75_, v___f_74_);
return v___x_76_;
}
}
static lean_object* _init_l_Lake_OrdPackageSet_empty(void){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Lake_OrdPackageSet_empty___closed__0, &l_Lake_OrdPackageSet_empty___closed__0_once, _init_l_Lake_OrdPackageSet_empty___closed__0);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___lam__0(lean_object* v_self_78_){
_start:
{
lean_inc_ref(v_self_78_);
return v_self_78_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___lam__0___boxed(lean_object* v_self_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lake_NPackage_instCoeOutPackage___lam__0(v_self_79_);
lean_dec_ref(v_self_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage(lean_object* v_n_82_){
_start:
{
lean_object* v___f_83_; 
v___f_83_ = ((lean_object*)(l_Lake_NPackage_instCoeOutPackage___closed__0));
return v___f_83_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___boxed(lean_object* v_n_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lake_NPackage_instCoeOutPackage(v_n_84_);
lean_dec(v_n_84_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeDepPackageKeyName(lean_object* v_pkg_86_){
_start:
{
lean_inc_ref(v_pkg_86_);
return v_pkg_86_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeDepPackageKeyName___boxed(lean_object* v_pkg_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lake_NPackage_instCoeDepPackageKeyName(v_pkg_87_);
lean_dec_ref(v_pkg_87_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___lam__0(lean_object* v_x_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_box(0);
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v___y_91_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___lam__0___boxed(lean_object* v_x_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lake_instInhabitedPostUpdateHook_default___lam__0(v_x_95_, v___y_96_, v___y_97_);
lean_dec(v___y_96_);
lean_dec_ref(v_x_95_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default(lean_object* v_a_101_){
_start:
{
lean_object* v___f_102_; 
v___f_102_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___closed__0));
return v___f_102_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___boxed(lean_object* v_a_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lake_instInhabitedPostUpdateHook_default(v_a_103_);
lean_dec(v_a_103_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook(lean_object* v_a_105_){
_start:
{
lean_object* v___f_106_; 
v___f_106_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___closed__0));
return v___f_106_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___boxed(lean_object* v_a_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lake_instInhabitedPostUpdateHook(v_a_107_);
lean_dec(v_a_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(lean_object* v_a_109_){
_start:
{
lean_inc_ref(v_a_109_);
return v_a_109_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg___boxed(lean_object* v_a_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(v_a_110_);
lean_dec_ref(v_a_110_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(lean_object* v_name_112_, lean_object* v_a_113_){
_start:
{
lean_inc_ref(v_a_113_);
return v_a_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed(lean_object* v_name_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(v_name_114_, v_a_115_);
lean_dec_ref(v_a_115_);
lean_dec(v_name_114_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeMk(lean_object* v_name_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_alloc_closure((void*)(l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed), 2, 1);
lean_closure_set(v___x_118_, 0, v_name_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(lean_object* v_a_119_){
_start:
{
lean_inc(v_a_119_);
return v_a_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg___boxed(lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(v_a_120_);
lean_dec(v_a_120_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(lean_object* v_name_122_, lean_object* v_a_123_){
_start:
{
lean_inc(v_a_123_);
return v_a_123_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed(lean_object* v_name_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(v_name_124_, v_a_125_);
lean_dec(v_a_125_);
lean_dec(v_name_124_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeGet(lean_object* v_name_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lean_alloc_closure((void*)(l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed), 2, 1);
lean_closure_set(v___x_128_, 0, v_name_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(lean_object* v_inst_129_){
_start:
{
lean_inc_ref(v_inst_129_);
return v_inst_129_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg___boxed(lean_object* v_inst_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(v_inst_130_);
lean_dec_ref(v_inst_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(lean_object* v_name_132_, lean_object* v_inst_133_){
_start:
{
lean_inc_ref(v_inst_133_);
return v_inst_133_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___boxed(lean_object* v_name_134_, lean_object* v_inst_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(v_name_134_, v_inst_135_);
lean_dec_ref(v_inst_135_);
lean_dec(v_name_134_);
return v_res_136_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isRoot(lean_object* v_self_144_){
_start:
{
lean_object* v_wsIdx_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v_wsIdx_145_ = lean_ctor_get(v_self_144_, 0);
v___x_146_ = lean_unsigned_to_nat(0u);
v___x_147_ = lean_nat_dec_eq(v_wsIdx_145_, v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isRoot___boxed(lean_object* v_self_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l_Lake_Package_isRoot(v_self_148_);
lean_dec_ref(v_self_148_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_bootstrap(lean_object* v_self_151_){
_start:
{
lean_object* v_config_152_; uint8_t v_bootstrap_153_; 
v_config_152_ = lean_ctor_get(v_self_151_, 6);
v_bootstrap_153_ = lean_ctor_get_uint8(v_config_152_, sizeof(void*)*26);
return v_bootstrap_153_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_bootstrap___boxed(lean_object* v_self_154_){
_start:
{
uint8_t v_res_155_; lean_object* v_r_156_; 
v_res_155_ = l_Lake_Package_bootstrap(v_self_154_);
lean_dec_ref(v_self_154_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_id_x3f(lean_object* v_self_157_){
_start:
{
lean_object* v_config_158_; uint8_t v_bootstrap_159_; 
v_config_158_ = lean_ctor_get(v_self_157_, 6);
v_bootstrap_159_ = lean_ctor_get_uint8(v_config_158_, sizeof(void*)*26);
if (v_bootstrap_159_ == 0)
{
lean_object* v_origName_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_origName_160_ = lean_ctor_get(v_self_157_, 3);
lean_inc(v_origName_160_);
lean_dec_ref(v_self_157_);
v___x_161_ = l_Lean_Name_toString(v_origName_160_, v_bootstrap_159_);
v___x_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
else
{
lean_object* v___x_163_; 
lean_dec_ref(v_self_157_);
v___x_163_ = lean_box(0);
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_version(lean_object* v_self_164_){
_start:
{
lean_object* v_config_165_; lean_object* v_version_166_; 
v_config_165_ = lean_ctor_get(v_self_164_, 6);
v_version_166_ = lean_ctor_get(v_config_165_, 16);
lean_inc_ref(v_version_166_);
return v_version_166_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_version___boxed(lean_object* v_self_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lake_Package_version(v_self_167_);
lean_dec_ref(v_self_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_versionTags(lean_object* v_self_169_){
_start:
{
lean_object* v_config_170_; lean_object* v_versionTags_171_; 
v_config_170_ = lean_ctor_get(v_self_169_, 6);
v_versionTags_171_ = lean_ctor_get(v_config_170_, 17);
lean_inc_ref(v_versionTags_171_);
return v_versionTags_171_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_versionTags___boxed(lean_object* v_self_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lake_Package_versionTags(v_self_172_);
lean_dec_ref(v_self_172_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_description(lean_object* v_self_174_){
_start:
{
lean_object* v_config_175_; lean_object* v_description_176_; 
v_config_175_ = lean_ctor_get(v_self_174_, 6);
v_description_176_ = lean_ctor_get(v_config_175_, 18);
lean_inc_ref(v_description_176_);
return v_description_176_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_description___boxed(lean_object* v_self_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lake_Package_description(v_self_177_);
lean_dec_ref(v_self_177_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_keywords(lean_object* v_self_179_){
_start:
{
lean_object* v_config_180_; lean_object* v_keywords_181_; 
v_config_180_ = lean_ctor_get(v_self_179_, 6);
v_keywords_181_ = lean_ctor_get(v_config_180_, 19);
lean_inc_ref(v_keywords_181_);
return v_keywords_181_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_keywords___boxed(lean_object* v_self_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lake_Package_keywords(v_self_182_);
lean_dec_ref(v_self_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_homepage(lean_object* v_self_184_){
_start:
{
lean_object* v_config_185_; lean_object* v_homepage_186_; 
v_config_185_ = lean_ctor_get(v_self_184_, 6);
v_homepage_186_ = lean_ctor_get(v_config_185_, 20);
lean_inc_ref(v_homepage_186_);
return v_homepage_186_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_homepage___boxed(lean_object* v_self_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lake_Package_homepage(v_self_187_);
lean_dec_ref(v_self_187_);
return v_res_188_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_reservoir(lean_object* v_self_189_){
_start:
{
lean_object* v_config_190_; uint8_t v_reservoir_191_; 
v_config_190_ = lean_ctor_get(v_self_189_, 6);
v_reservoir_191_ = lean_ctor_get_uint8(v_config_190_, sizeof(void*)*26 + 3);
return v_reservoir_191_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoir___boxed(lean_object* v_self_192_){
_start:
{
uint8_t v_res_193_; lean_object* v_r_194_; 
v_res_193_ = l_Lake_Package_reservoir(v_self_192_);
lean_dec_ref(v_self_192_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_license(lean_object* v_self_195_){
_start:
{
lean_object* v_config_196_; lean_object* v_license_197_; 
v_config_196_ = lean_ctor_get(v_self_195_, 6);
v_license_197_ = lean_ctor_get(v_config_196_, 21);
lean_inc_ref(v_license_197_);
return v_license_197_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_license___boxed(lean_object* v_self_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lake_Package_license(v_self_198_);
lean_dec_ref(v_self_198_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLicenseFiles(lean_object* v_self_220_){
_start:
{
lean_object* v_config_221_; lean_object* v_licenseFiles_222_; lean_object* v___f_223_; lean_object* v___x_224_; size_t v_sz_225_; size_t v___x_226_; lean_object* v___x_227_; 
v_config_221_ = lean_ctor_get(v_self_220_, 6);
lean_inc_ref(v_config_221_);
lean_dec_ref(v_self_220_);
v_licenseFiles_222_ = lean_ctor_get(v_config_221_, 22);
lean_inc_ref(v_licenseFiles_222_);
lean_dec_ref(v_config_221_);
v___f_223_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__0));
v___x_224_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__10));
v_sz_225_ = lean_array_size(v_licenseFiles_222_);
v___x_226_ = ((size_t)0ULL);
v___x_227_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_224_, v___f_223_, v_sz_225_, v___x_226_, v_licenseFiles_222_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles___lam__0(lean_object* v_dir_228_, lean_object* v_x_229_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = l_System_FilePath_normalize(v_x_229_);
v___x_231_ = l_Lake_joinRelative(v_dir_228_, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles(lean_object* v_self_232_){
_start:
{
lean_object* v_config_233_; lean_object* v_dir_234_; lean_object* v_licenseFiles_235_; lean_object* v___f_236_; lean_object* v___f_237_; lean_object* v___x_238_; size_t v_sz_239_; size_t v___x_240_; lean_object* v___x_241_; size_t v_sz_242_; lean_object* v___x_243_; 
v_config_233_ = lean_ctor_get(v_self_232_, 6);
lean_inc_ref(v_config_233_);
v_dir_234_ = lean_ctor_get(v_self_232_, 4);
lean_inc_ref(v_dir_234_);
lean_dec_ref(v_self_232_);
v_licenseFiles_235_ = lean_ctor_get(v_config_233_, 22);
lean_inc_ref(v_licenseFiles_235_);
lean_dec_ref(v_config_233_);
v___f_236_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__0));
v___f_237_ = lean_alloc_closure((void*)(l_Lake_Package_licenseFiles___lam__0), 2, 1);
lean_closure_set(v___f_237_, 0, v_dir_234_);
v___x_238_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__10));
v_sz_239_ = lean_array_size(v_licenseFiles_235_);
v___x_240_ = ((size_t)0ULL);
v___x_241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_238_, v___f_236_, v_sz_239_, v___x_240_, v_licenseFiles_235_);
v_sz_242_ = lean_array_size(v___x_241_);
v___x_243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_238_, v___f_237_, v_sz_242_, v___x_240_, v___x_241_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relReadmeFile(lean_object* v_self_244_){
_start:
{
lean_object* v_config_245_; lean_object* v_readmeFile_246_; lean_object* v___x_247_; 
v_config_245_ = lean_ctor_get(v_self_244_, 6);
lean_inc_ref(v_config_245_);
lean_dec_ref(v_self_244_);
v_readmeFile_246_ = lean_ctor_get(v_config_245_, 23);
lean_inc_ref(v_readmeFile_246_);
lean_dec_ref(v_config_245_);
v___x_247_ = l_System_FilePath_normalize(v_readmeFile_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_readmeFile(lean_object* v_self_248_){
_start:
{
lean_object* v_config_249_; lean_object* v_dir_250_; lean_object* v_readmeFile_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_config_249_ = lean_ctor_get(v_self_248_, 6);
lean_inc_ref(v_config_249_);
v_dir_250_ = lean_ctor_get(v_self_248_, 4);
lean_inc_ref(v_dir_250_);
lean_dec_ref(v_self_248_);
v_readmeFile_251_ = lean_ctor_get(v_config_249_, 23);
lean_inc_ref(v_readmeFile_251_);
lean_dec_ref(v_config_249_);
v___x_252_ = l_System_FilePath_normalize(v_readmeFile_251_);
v___x_253_ = l_Lake_joinRelative(v_dir_250_, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir(lean_object* v_x_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lake_defaultLakeDir;
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___boxed(lean_object* v_x_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lake_Package_relLakeDir(v_x_256_);
lean_dec_ref(v_x_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lakeDir(lean_object* v_self_258_){
_start:
{
lean_object* v_dir_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v_dir_259_ = lean_ctor_get(v_self_258_, 4);
lean_inc_ref(v_dir_259_);
lean_dec_ref(v_self_258_);
v___x_260_ = l_Lake_defaultLakeDir;
v___x_261_ = l_Lake_joinRelative(v_dir_259_, v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relPkgsDir(lean_object* v_self_262_){
_start:
{
lean_object* v_config_263_; lean_object* v_toWorkspaceConfig_264_; lean_object* v___x_265_; 
v_config_263_ = lean_ctor_get(v_self_262_, 6);
lean_inc_ref(v_config_263_);
lean_dec_ref(v_self_262_);
v_toWorkspaceConfig_264_ = lean_ctor_get(v_config_263_, 0);
lean_inc_ref(v_toWorkspaceConfig_264_);
lean_dec_ref(v_config_263_);
v___x_265_ = l_System_FilePath_normalize(v_toWorkspaceConfig_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_pkgsDir(lean_object* v_self_266_){
_start:
{
lean_object* v_config_267_; lean_object* v_dir_268_; lean_object* v_toWorkspaceConfig_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v_config_267_ = lean_ctor_get(v_self_266_, 6);
lean_inc_ref(v_config_267_);
v_dir_268_ = lean_ctor_get(v_self_266_, 4);
lean_inc_ref(v_dir_268_);
lean_dec_ref(v_self_266_);
v_toWorkspaceConfig_269_ = lean_ctor_get(v_config_267_, 0);
lean_inc_ref(v_toWorkspaceConfig_269_);
lean_dec_ref(v_config_267_);
v___x_270_ = l_System_FilePath_normalize(v_toWorkspaceConfig_269_);
v___x_271_ = l_Lake_joinRelative(v_dir_268_, v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_manifestFile(lean_object* v_self_272_){
_start:
{
lean_object* v_dir_273_; lean_object* v_relManifestFile_274_; lean_object* v___x_275_; 
v_dir_273_ = lean_ctor_get(v_self_272_, 4);
lean_inc_ref(v_dir_273_);
v_relManifestFile_274_ = lean_ctor_get(v_self_272_, 9);
lean_inc_ref(v_relManifestFile_274_);
lean_dec_ref(v_self_272_);
v___x_275_ = l_Lake_joinRelative(v_dir_273_, v_relManifestFile_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildDir(lean_object* v_self_276_){
_start:
{
lean_object* v_config_277_; lean_object* v_dir_278_; lean_object* v_buildDir_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v_config_277_ = lean_ctor_get(v_self_276_, 6);
lean_inc_ref(v_config_277_);
v_dir_278_ = lean_ctor_get(v_self_276_, 4);
lean_inc_ref(v_dir_278_);
lean_dec_ref(v_self_276_);
v_buildDir_279_ = lean_ctor_get(v_config_277_, 5);
lean_inc_ref(v_buildDir_279_);
lean_dec_ref(v_config_277_);
v___x_280_ = l_System_FilePath_normalize(v_buildDir_279_);
v___x_281_ = l_Lake_joinRelative(v_dir_278_, v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs(lean_object* v_self_282_){
_start:
{
lean_object* v_config_283_; lean_object* v_testDriverArgs_284_; 
v_config_283_ = lean_ctor_get(v_self_282_, 6);
v_testDriverArgs_284_ = lean_ctor_get(v_config_283_, 13);
lean_inc_ref(v_testDriverArgs_284_);
return v_testDriverArgs_284_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs___boxed(lean_object* v_self_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lake_Package_testDriverArgs(v_self_285_);
lean_dec_ref(v_self_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs(lean_object* v_self_287_){
_start:
{
lean_object* v_config_288_; lean_object* v_lintDriverArgs_289_; 
v_config_288_ = lean_ctor_get(v_self_287_, 6);
v_lintDriverArgs_289_ = lean_ctor_get(v_config_288_, 15);
lean_inc_ref(v_lintDriverArgs_289_);
return v_lintDriverArgs_289_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs___boxed(lean_object* v_self_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lake_Package_lintDriverArgs(v_self_290_);
lean_dec_ref(v_self_290_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets(lean_object* v_self_292_){
_start:
{
lean_object* v_config_293_; lean_object* v_extraDepTargets_294_; 
v_config_293_ = lean_ctor_get(v_self_292_, 6);
v_extraDepTargets_294_ = lean_ctor_get(v_config_293_, 2);
lean_inc_ref(v_extraDepTargets_294_);
return v_extraDepTargets_294_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets___boxed(lean_object* v_self_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lake_Package_extraDepTargets(v_self_295_);
lean_dec_ref(v_self_295_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent(lean_object* v_self_297_){
_start:
{
lean_object* v_config_298_; lean_object* v_toLeanConfig_299_; lean_object* v_platformIndependent_300_; 
v_config_298_ = lean_ctor_get(v_self_297_, 6);
v_toLeanConfig_299_ = lean_ctor_get(v_config_298_, 1);
v_platformIndependent_300_ = lean_ctor_get(v_toLeanConfig_299_, 10);
lean_inc(v_platformIndependent_300_);
return v_platformIndependent_300_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent___boxed(lean_object* v_self_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lake_Package_platformIndependent(v_self_301_);
lean_dec_ref(v_self_301_);
return v_res_302_;
}
}
static lean_object* _init_l_Lake_Package_isPlatformIndependent___closed__0(void){
_start:
{
lean_object* v___x_303_; lean_object* v___f_304_; 
v___x_303_ = lean_alloc_closure((void*)(l_instDecidableEqBool___boxed), 2, 0);
v___f_304_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_304_, 0, v___x_303_);
return v___f_304_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isPlatformIndependent(lean_object* v_self_308_){
_start:
{
lean_object* v_config_309_; lean_object* v_toLeanConfig_310_; lean_object* v_platformIndependent_311_; lean_object* v___f_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
v_config_309_ = lean_ctor_get(v_self_308_, 6);
lean_inc_ref(v_config_309_);
lean_dec_ref(v_self_308_);
v_toLeanConfig_310_ = lean_ctor_get(v_config_309_, 1);
lean_inc_ref(v_toLeanConfig_310_);
lean_dec_ref(v_config_309_);
v_platformIndependent_311_ = lean_ctor_get(v_toLeanConfig_310_, 10);
lean_inc(v_platformIndependent_311_);
lean_dec_ref(v_toLeanConfig_310_);
v___f_312_ = lean_obj_once(&l_Lake_Package_isPlatformIndependent___closed__0, &l_Lake_Package_isPlatformIndependent___closed__0_once, _init_l_Lake_Package_isPlatformIndependent___closed__0);
v___x_313_ = ((lean_object*)(l_Lake_Package_isPlatformIndependent___closed__1));
v___x_314_ = l_Option_instBEq_beq___redArg(v___f_312_, v_platformIndependent_311_, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isPlatformIndependent___boxed(lean_object* v_self_315_){
_start:
{
uint8_t v_res_316_; lean_object* v_r_317_; 
v_res_316_ = l_Lake_Package_isPlatformIndependent(v_self_315_);
v_r_317_ = lean_box(v_res_316_);
return v_r_317_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_fixedToolchain(lean_object* v_self_318_){
_start:
{
lean_object* v_config_319_; uint8_t v_fixedToolchain_320_; 
v_config_319_ = lean_ctor_get(v_self_318_, 6);
v_fixedToolchain_320_ = lean_ctor_get_uint8(v_config_319_, sizeof(void*)*26 + 6);
return v_fixedToolchain_320_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fixedToolchain___boxed(lean_object* v_self_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l_Lake_Package_fixedToolchain(v_self_321_);
lean_dec_ref(v_self_321_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f(lean_object* v_self_324_){
_start:
{
lean_object* v_config_325_; lean_object* v_releaseRepo_326_; 
v_config_325_ = lean_ctor_get(v_self_324_, 6);
v_releaseRepo_326_ = lean_ctor_get(v_config_325_, 10);
lean_inc(v_releaseRepo_326_);
return v_releaseRepo_326_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f___boxed(lean_object* v_self_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lake_Package_releaseRepo_x3f(v_self_327_);
lean_dec_ref(v_self_327_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f(lean_object* v_self_329_){
_start:
{
lean_object* v_remoteUrl_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v_remoteUrl_330_ = lean_ctor_get(v_self_329_, 11);
v___x_331_ = lean_string_utf8_byte_size(v_remoteUrl_330_);
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = lean_nat_dec_eq(v___x_331_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; 
v___x_334_ = lean_box(0);
return v___x_334_;
}
else
{
lean_object* v___x_335_; 
lean_inc_ref(v_remoteUrl_330_);
v___x_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_335_, 0, v_remoteUrl_330_);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f___boxed(lean_object* v_self_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lake_Package_remoteUrl_x3f(v_self_336_);
lean_dec_ref(v_self_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildArchiveFile(lean_object* v_self_338_){
_start:
{
lean_object* v_dir_339_; lean_object* v_buildArchive_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_dir_339_ = lean_ctor_get(v_self_338_, 4);
lean_inc_ref(v_dir_339_);
v_buildArchive_340_ = lean_ctor_get(v_self_338_, 19);
lean_inc_ref(v_buildArchive_340_);
lean_dec_ref(v_self_338_);
v___x_341_ = l_Lake_defaultLakeDir;
v___x_342_ = l_Lake_joinRelative(v_dir_339_, v___x_341_);
v___x_343_ = l_Lake_joinRelative(v___x_342_, v_buildArchive_340_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFile(lean_object* v_self_345_){
_start:
{
lean_object* v_dir_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_dir_346_ = lean_ctor_get(v_self_345_, 4);
lean_inc_ref(v_dir_346_);
lean_dec_ref(v_self_345_);
v___x_347_ = l_Lake_defaultLakeDir;
v___x_348_ = l_Lake_joinRelative(v_dir_346_, v___x_347_);
v___x_349_ = ((lean_object*)(l_Lake_Package_barrelFile___closed__0));
v___x_350_ = l_Lake_joinRelative(v___x_348_, v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_preferReleaseBuild(lean_object* v_self_351_){
_start:
{
lean_object* v_config_352_; uint8_t v_preferReleaseBuild_353_; 
v_config_352_ = lean_ctor_get(v_self_351_, 6);
v_preferReleaseBuild_353_ = lean_ctor_get_uint8(v_config_352_, sizeof(void*)*26 + 2);
return v_preferReleaseBuild_353_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_preferReleaseBuild___boxed(lean_object* v_self_354_){
_start:
{
uint8_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l_Lake_Package_preferReleaseBuild(v_self_354_);
lean_dec_ref(v_self_354_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_precompileModules(lean_object* v_self_357_){
_start:
{
lean_object* v_config_358_; uint8_t v_precompileModules_359_; 
v_config_358_ = lean_ctor_get(v_self_357_, 6);
v_precompileModules_359_ = lean_ctor_get_uint8(v_config_358_, sizeof(void*)*26 + 1);
return v_precompileModules_359_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_precompileModules___boxed(lean_object* v_self_360_){
_start:
{
uint8_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_Lake_Package_precompileModules(v_self_360_);
lean_dec_ref(v_self_360_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs(lean_object* v_self_363_){
_start:
{
lean_object* v_config_364_; lean_object* v_moreGlobalServerArgs_365_; 
v_config_364_ = lean_ctor_get(v_self_363_, 6);
v_moreGlobalServerArgs_365_ = lean_ctor_get(v_config_364_, 3);
lean_inc_ref(v_moreGlobalServerArgs_365_);
return v_moreGlobalServerArgs_365_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs___boxed(lean_object* v_self_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lake_Package_moreGlobalServerArgs(v_self_366_);
lean_dec_ref(v_self_366_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions(lean_object* v_self_368_){
_start:
{
lean_object* v_config_369_; lean_object* v_toLeanConfig_370_; lean_object* v_leanOptions_371_; lean_object* v_moreServerOptions_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_config_369_ = lean_ctor_get(v_self_368_, 6);
v_toLeanConfig_370_ = lean_ctor_get(v_config_369_, 1);
v_leanOptions_371_ = lean_ctor_get(v_toLeanConfig_370_, 0);
v_moreServerOptions_372_ = lean_ctor_get(v_toLeanConfig_370_, 4);
v___x_373_ = l_Lean_LeanOptions_ofArray(v_leanOptions_371_);
v___x_374_ = l_Lean_LeanOptions_appendArray(v___x_373_, v_moreServerOptions_372_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions___boxed(lean_object* v_self_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lake_Package_moreServerOptions(v_self_375_);
lean_dec_ref(v_self_375_);
return v_res_376_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_buildType(lean_object* v_self_377_){
_start:
{
lean_object* v_config_378_; lean_object* v_toLeanConfig_379_; uint8_t v_buildType_380_; 
v_config_378_ = lean_ctor_get(v_self_377_, 6);
v_toLeanConfig_379_ = lean_ctor_get(v_config_378_, 1);
v_buildType_380_ = lean_ctor_get_uint8(v_toLeanConfig_379_, sizeof(void*)*13);
return v_buildType_380_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildType___boxed(lean_object* v_self_381_){
_start:
{
uint8_t v_res_382_; lean_object* v_r_383_; 
v_res_382_ = l_Lake_Package_buildType(v_self_381_);
lean_dec_ref(v_self_381_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_backend(lean_object* v_self_384_){
_start:
{
lean_object* v_config_385_; lean_object* v_toLeanConfig_386_; uint8_t v_backend_387_; 
v_config_385_ = lean_ctor_get(v_self_384_, 6);
v_toLeanConfig_386_ = lean_ctor_get(v_config_385_, 1);
v_backend_387_ = lean_ctor_get_uint8(v_toLeanConfig_386_, sizeof(void*)*13 + 1);
return v_backend_387_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_backend___boxed(lean_object* v_self_388_){
_start:
{
uint8_t v_res_389_; lean_object* v_r_390_; 
v_res_389_ = l_Lake_Package_backend(v_self_388_);
lean_dec_ref(v_self_388_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_allowImportAll(lean_object* v_self_391_){
_start:
{
lean_object* v_config_392_; uint8_t v_allowImportAll_393_; 
v_config_392_ = lean_ctor_get(v_self_391_, 6);
v_allowImportAll_393_ = lean_ctor_get_uint8(v_config_392_, sizeof(void*)*26 + 5);
return v_allowImportAll_393_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_allowImportAll___boxed(lean_object* v_self_394_){
_start:
{
uint8_t v_res_395_; lean_object* v_r_396_; 
v_res_395_ = l_Lake_Package_allowImportAll(v_self_394_);
lean_dec_ref(v_self_394_);
v_r_396_ = lean_box(v_res_395_);
return v_r_396_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs(lean_object* v_self_397_){
_start:
{
lean_object* v_config_398_; lean_object* v_toLeanConfig_399_; lean_object* v_dynlibs_400_; 
v_config_398_ = lean_ctor_get(v_self_397_, 6);
v_toLeanConfig_399_ = lean_ctor_get(v_config_398_, 1);
v_dynlibs_400_ = lean_ctor_get(v_toLeanConfig_399_, 11);
lean_inc_ref(v_dynlibs_400_);
return v_dynlibs_400_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs___boxed(lean_object* v_self_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lake_Package_dynlibs(v_self_401_);
lean_dec_ref(v_self_401_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins(lean_object* v_self_403_){
_start:
{
lean_object* v_config_404_; lean_object* v_toLeanConfig_405_; lean_object* v_plugins_406_; 
v_config_404_ = lean_ctor_get(v_self_403_, 6);
v_toLeanConfig_405_ = lean_ctor_get(v_config_404_, 1);
v_plugins_406_ = lean_ctor_get(v_toLeanConfig_405_, 12);
lean_inc_ref(v_plugins_406_);
return v_plugins_406_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins___boxed(lean_object* v_self_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lake_Package_plugins(v_self_407_);
lean_dec_ref(v_self_407_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions(lean_object* v_self_409_){
_start:
{
lean_object* v_config_410_; lean_object* v_toLeanConfig_411_; lean_object* v_leanOptions_412_; lean_object* v___x_413_; 
v_config_410_ = lean_ctor_get(v_self_409_, 6);
v_toLeanConfig_411_ = lean_ctor_get(v_config_410_, 1);
v_leanOptions_412_ = lean_ctor_get(v_toLeanConfig_411_, 0);
v___x_413_ = l_Lean_LeanOptions_ofArray(v_leanOptions_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions___boxed(lean_object* v_self_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lake_Package_leanOptions(v_self_414_);
lean_dec_ref(v_self_414_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs(lean_object* v_self_416_){
_start:
{
lean_object* v_config_417_; lean_object* v_toLeanConfig_418_; lean_object* v_moreLeanArgs_419_; 
v_config_417_ = lean_ctor_get(v_self_416_, 6);
v_toLeanConfig_418_ = lean_ctor_get(v_config_417_, 1);
v_moreLeanArgs_419_ = lean_ctor_get(v_toLeanConfig_418_, 1);
lean_inc_ref(v_moreLeanArgs_419_);
return v_moreLeanArgs_419_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs___boxed(lean_object* v_self_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lake_Package_moreLeanArgs(v_self_420_);
lean_dec_ref(v_self_420_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs(lean_object* v_self_422_){
_start:
{
lean_object* v_config_423_; lean_object* v_toLeanConfig_424_; lean_object* v_weakLeanArgs_425_; 
v_config_423_ = lean_ctor_get(v_self_422_, 6);
v_toLeanConfig_424_ = lean_ctor_get(v_config_423_, 1);
v_weakLeanArgs_425_ = lean_ctor_get(v_toLeanConfig_424_, 2);
lean_inc_ref(v_weakLeanArgs_425_);
return v_weakLeanArgs_425_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs___boxed(lean_object* v_self_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lake_Package_weakLeanArgs(v_self_426_);
lean_dec_ref(v_self_426_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs(lean_object* v_self_428_){
_start:
{
lean_object* v_config_429_; lean_object* v_toLeanConfig_430_; lean_object* v_moreLeancArgs_431_; 
v_config_429_ = lean_ctor_get(v_self_428_, 6);
v_toLeanConfig_430_ = lean_ctor_get(v_config_429_, 1);
v_moreLeancArgs_431_ = lean_ctor_get(v_toLeanConfig_430_, 3);
lean_inc_ref(v_moreLeancArgs_431_);
return v_moreLeancArgs_431_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs___boxed(lean_object* v_self_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lake_Package_moreLeancArgs(v_self_432_);
lean_dec_ref(v_self_432_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs(lean_object* v_self_434_){
_start:
{
lean_object* v_config_435_; lean_object* v_toLeanConfig_436_; lean_object* v_weakLeancArgs_437_; 
v_config_435_ = lean_ctor_get(v_self_434_, 6);
v_toLeanConfig_436_ = lean_ctor_get(v_config_435_, 1);
v_weakLeancArgs_437_ = lean_ctor_get(v_toLeanConfig_436_, 5);
lean_inc_ref(v_weakLeancArgs_437_);
return v_weakLeancArgs_437_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs___boxed(lean_object* v_self_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lake_Package_weakLeancArgs(v_self_438_);
lean_dec_ref(v_self_438_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs(lean_object* v_self_440_){
_start:
{
lean_object* v_config_441_; lean_object* v_toLeanConfig_442_; lean_object* v_moreLinkObjs_443_; 
v_config_441_ = lean_ctor_get(v_self_440_, 6);
v_toLeanConfig_442_ = lean_ctor_get(v_config_441_, 1);
v_moreLinkObjs_443_ = lean_ctor_get(v_toLeanConfig_442_, 6);
lean_inc_ref(v_moreLinkObjs_443_);
return v_moreLinkObjs_443_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs___boxed(lean_object* v_self_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lake_Package_moreLinkObjs(v_self_444_);
lean_dec_ref(v_self_444_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs(lean_object* v_self_446_){
_start:
{
lean_object* v_config_447_; lean_object* v_toLeanConfig_448_; lean_object* v_moreLinkLibs_449_; 
v_config_447_ = lean_ctor_get(v_self_446_, 6);
v_toLeanConfig_448_ = lean_ctor_get(v_config_447_, 1);
v_moreLinkLibs_449_ = lean_ctor_get(v_toLeanConfig_448_, 7);
lean_inc_ref(v_moreLinkLibs_449_);
return v_moreLinkLibs_449_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs___boxed(lean_object* v_self_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lake_Package_moreLinkLibs(v_self_450_);
lean_dec_ref(v_self_450_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs(lean_object* v_self_452_){
_start:
{
lean_object* v_config_453_; lean_object* v_toLeanConfig_454_; lean_object* v_moreLinkArgs_455_; 
v_config_453_ = lean_ctor_get(v_self_452_, 6);
v_toLeanConfig_454_ = lean_ctor_get(v_config_453_, 1);
v_moreLinkArgs_455_ = lean_ctor_get(v_toLeanConfig_454_, 8);
lean_inc_ref(v_moreLinkArgs_455_);
return v_moreLinkArgs_455_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs___boxed(lean_object* v_self_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lake_Package_moreLinkArgs(v_self_456_);
lean_dec_ref(v_self_456_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs(lean_object* v_self_458_){
_start:
{
lean_object* v_config_459_; lean_object* v_toLeanConfig_460_; lean_object* v_weakLinkArgs_461_; 
v_config_459_ = lean_ctor_get(v_self_458_, 6);
v_toLeanConfig_460_ = lean_ctor_get(v_config_459_, 1);
v_weakLinkArgs_461_ = lean_ctor_get(v_toLeanConfig_460_, 9);
lean_inc_ref(v_weakLinkArgs_461_);
return v_weakLinkArgs_461_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs___boxed(lean_object* v_self_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lake_Package_weakLinkArgs(v_self_462_);
lean_dec_ref(v_self_462_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_srcDir(lean_object* v_self_464_){
_start:
{
lean_object* v_config_465_; lean_object* v_dir_466_; lean_object* v_srcDir_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v_config_465_ = lean_ctor_get(v_self_464_, 6);
lean_inc_ref(v_config_465_);
v_dir_466_ = lean_ctor_get(v_self_464_, 4);
lean_inc_ref(v_dir_466_);
lean_dec_ref(v_self_464_);
v_srcDir_467_ = lean_ctor_get(v_config_465_, 4);
lean_inc_ref(v_srcDir_467_);
lean_dec_ref(v_config_465_);
v___x_468_ = l_System_FilePath_normalize(v_srcDir_467_);
v___x_469_ = l_Lake_joinRelative(v_dir_466_, v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_rootDir(lean_object* v_self_470_){
_start:
{
lean_object* v_config_471_; lean_object* v_dir_472_; lean_object* v_srcDir_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_config_471_ = lean_ctor_get(v_self_470_, 6);
lean_inc_ref(v_config_471_);
v_dir_472_ = lean_ctor_get(v_self_470_, 4);
lean_inc_ref(v_dir_472_);
lean_dec_ref(v_self_470_);
v_srcDir_473_ = lean_ctor_get(v_config_471_, 4);
lean_inc_ref(v_srcDir_473_);
lean_dec_ref(v_config_471_);
v___x_474_ = l_System_FilePath_normalize(v_srcDir_473_);
v___x_475_ = l_Lake_joinRelative(v_dir_472_, v___x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanLibDir(lean_object* v_self_476_){
_start:
{
lean_object* v_config_477_; lean_object* v_dir_478_; lean_object* v_buildDir_479_; lean_object* v_leanLibDir_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_config_477_ = lean_ctor_get(v_self_476_, 6);
lean_inc_ref(v_config_477_);
v_dir_478_ = lean_ctor_get(v_self_476_, 4);
lean_inc_ref(v_dir_478_);
lean_dec_ref(v_self_476_);
v_buildDir_479_ = lean_ctor_get(v_config_477_, 5);
lean_inc_ref(v_buildDir_479_);
v_leanLibDir_480_ = lean_ctor_get(v_config_477_, 6);
lean_inc_ref(v_leanLibDir_480_);
lean_dec_ref(v_config_477_);
v___x_481_ = l_System_FilePath_normalize(v_buildDir_479_);
v___x_482_ = l_Lake_joinRelative(v_dir_478_, v___x_481_);
v___x_483_ = l_System_FilePath_normalize(v_leanLibDir_480_);
v___x_484_ = l_Lake_joinRelative(v___x_482_, v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_staticLibDir(lean_object* v_self_485_){
_start:
{
lean_object* v_config_486_; lean_object* v_dir_487_; lean_object* v_buildDir_488_; lean_object* v_nativeLibDir_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_config_486_ = lean_ctor_get(v_self_485_, 6);
lean_inc_ref(v_config_486_);
v_dir_487_ = lean_ctor_get(v_self_485_, 4);
lean_inc_ref(v_dir_487_);
lean_dec_ref(v_self_485_);
v_buildDir_488_ = lean_ctor_get(v_config_486_, 5);
lean_inc_ref(v_buildDir_488_);
v_nativeLibDir_489_ = lean_ctor_get(v_config_486_, 7);
lean_inc_ref(v_nativeLibDir_489_);
lean_dec_ref(v_config_486_);
v___x_490_ = l_System_FilePath_normalize(v_buildDir_488_);
v___x_491_ = l_Lake_joinRelative(v_dir_487_, v___x_490_);
v___x_492_ = l_System_FilePath_normalize(v_nativeLibDir_489_);
v___x_493_ = l_Lake_joinRelative(v___x_491_, v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_sharedLibDir(lean_object* v_self_494_){
_start:
{
lean_object* v_config_495_; lean_object* v_dir_496_; lean_object* v_buildDir_497_; lean_object* v_nativeLibDir_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v_config_495_ = lean_ctor_get(v_self_494_, 6);
lean_inc_ref(v_config_495_);
v_dir_496_ = lean_ctor_get(v_self_494_, 4);
lean_inc_ref(v_dir_496_);
lean_dec_ref(v_self_494_);
v_buildDir_497_ = lean_ctor_get(v_config_495_, 5);
lean_inc_ref(v_buildDir_497_);
v_nativeLibDir_498_ = lean_ctor_get(v_config_495_, 7);
lean_inc_ref(v_nativeLibDir_498_);
lean_dec_ref(v_config_495_);
v___x_499_ = l_System_FilePath_normalize(v_buildDir_497_);
v___x_500_ = l_Lake_joinRelative(v_dir_496_, v___x_499_);
v___x_501_ = l_System_FilePath_normalize(v_nativeLibDir_498_);
v___x_502_ = l_Lake_joinRelative(v___x_500_, v___x_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_binDir(lean_object* v_self_503_){
_start:
{
lean_object* v_config_504_; lean_object* v_dir_505_; lean_object* v_buildDir_506_; lean_object* v_binDir_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v_config_504_ = lean_ctor_get(v_self_503_, 6);
lean_inc_ref(v_config_504_);
v_dir_505_ = lean_ctor_get(v_self_503_, 4);
lean_inc_ref(v_dir_505_);
lean_dec_ref(v_self_503_);
v_buildDir_506_ = lean_ctor_get(v_config_504_, 5);
lean_inc_ref(v_buildDir_506_);
v_binDir_507_ = lean_ctor_get(v_config_504_, 8);
lean_inc_ref(v_binDir_507_);
lean_dec_ref(v_config_504_);
v___x_508_ = l_System_FilePath_normalize(v_buildDir_506_);
v___x_509_ = l_Lake_joinRelative(v_dir_505_, v___x_508_);
v___x_510_ = l_System_FilePath_normalize(v_binDir_507_);
v___x_511_ = l_Lake_joinRelative(v___x_509_, v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_irDir(lean_object* v_self_512_){
_start:
{
lean_object* v_config_513_; lean_object* v_dir_514_; lean_object* v_buildDir_515_; lean_object* v_irDir_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_config_513_ = lean_ctor_get(v_self_512_, 6);
lean_inc_ref(v_config_513_);
v_dir_514_ = lean_ctor_get(v_self_512_, 4);
lean_inc_ref(v_dir_514_);
lean_dec_ref(v_self_512_);
v_buildDir_515_ = lean_ctor_get(v_config_513_, 5);
lean_inc_ref(v_buildDir_515_);
v_irDir_516_ = lean_ctor_get(v_config_513_, 9);
lean_inc_ref(v_irDir_516_);
lean_dec_ref(v_config_513_);
v___x_517_ = l_System_FilePath_normalize(v_buildDir_515_);
v___x_518_ = l_Lake_joinRelative(v_dir_514_, v___x_517_);
v___x_519_ = l_System_FilePath_normalize(v_irDir_516_);
v___x_520_ = l_Lake_joinRelative(v___x_518_, v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_libPrefixOnWindows(lean_object* v_self_521_){
_start:
{
lean_object* v_config_522_; uint8_t v_libPrefixOnWindows_523_; 
v_config_522_ = lean_ctor_get(v_self_521_, 6);
v_libPrefixOnWindows_523_ = lean_ctor_get_uint8(v_config_522_, sizeof(void*)*26 + 4);
return v_libPrefixOnWindows_523_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_libPrefixOnWindows___boxed(lean_object* v_self_524_){
_start:
{
uint8_t v_res_525_; lean_object* v_r_526_; 
v_res_525_ = l_Lake_Package_libPrefixOnWindows(v_self_524_);
lean_dec_ref(v_self_524_);
v_r_526_ = lean_box(v_res_525_);
return v_r_526_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f(lean_object* v_self_527_){
_start:
{
lean_object* v_config_528_; lean_object* v_enableArtifactCache_x3f_529_; 
v_config_528_ = lean_ctor_get(v_self_527_, 6);
v_enableArtifactCache_x3f_529_ = lean_ctor_get(v_config_528_, 24);
lean_inc(v_enableArtifactCache_x3f_529_);
return v_enableArtifactCache_x3f_529_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f___boxed(lean_object* v_self_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lake_Package_enableArtifactCache_x3f(v_self_530_);
lean_dec_ref(v_self_530_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f(lean_object* v_self_532_){
_start:
{
lean_object* v_config_533_; lean_object* v_restoreAllArtifacts_x3f_534_; 
v_config_533_ = lean_ctor_get(v_self_532_, 6);
v_restoreAllArtifacts_x3f_534_ = lean_ctor_get(v_config_533_, 25);
lean_inc(v_restoreAllArtifacts_x3f_534_);
return v_restoreAllArtifacts_x3f_534_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f___boxed(lean_object* v_self_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lake_Package_restoreAllArtifacts_x3f(v_self_535_);
lean_dec_ref(v_self_535_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_cacheScope(lean_object* v_self_537_){
_start:
{
lean_object* v_baseName_538_; uint8_t v___x_539_; lean_object* v___x_540_; 
v_baseName_538_ = lean_ctor_get(v_self_537_, 1);
lean_inc(v_baseName_538_);
lean_dec_ref(v_self_537_);
v___x_539_ = 0;
v___x_540_ = l_Lean_Name_toString(v_baseName_538_, v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(lean_object* v_self_542_){
_start:
{
lean_object* v_origName_543_; lean_object* v_scope_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v_origName_543_ = lean_ctor_get(v_self_542_, 3);
lean_inc(v_origName_543_);
v_scope_544_ = lean_ctor_get(v_self_542_, 10);
lean_inc_ref(v_scope_544_);
lean_dec_ref(v_self_542_);
v___x_545_ = ((lean_object*)(l___private_Lake_Config_Package_0__Lake_Package_reservoirScope___closed__0));
v___x_546_ = lean_string_append(v_scope_544_, v___x_545_);
v___x_547_ = 0;
v___x_548_ = l_Lean_Name_toString(v_origName_543_, v___x_547_);
v___x_549_ = lean_string_append(v___x_546_, v___x_548_);
lean_dec_ref(v___x_548_);
v___x_550_ = l_Lake_CacheServiceScope_ofString(v___x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirScope_x3f(lean_object* v_self_551_){
_start:
{
lean_object* v_scope_552_; lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v_scope_552_ = lean_ctor_get(v_self_551_, 10);
v___x_553_ = lean_string_utf8_byte_size(v_scope_552_);
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = lean_nat_dec_eq(v___x_553_, v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(v_self_551_);
v___x_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
return v___x_557_;
}
else
{
lean_object* v___x_558_; 
lean_dec_ref(v_self_551_);
v___x_558_ = lean_box(0);
return v___x_558_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(lean_object* v_t_559_, lean_object* v_k_560_){
_start:
{
if (lean_obj_tag(v_t_559_) == 0)
{
lean_object* v_k_561_; lean_object* v_v_562_; lean_object* v_l_563_; lean_object* v_r_564_; uint8_t v___x_565_; 
v_k_561_ = lean_ctor_get(v_t_559_, 1);
v_v_562_ = lean_ctor_get(v_t_559_, 2);
v_l_563_ = lean_ctor_get(v_t_559_, 3);
v_r_564_ = lean_ctor_get(v_t_559_, 4);
v___x_565_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_560_, v_k_561_);
switch(v___x_565_)
{
case 0:
{
v_t_559_ = v_l_563_;
goto _start;
}
case 1:
{
lean_object* v___x_567_; 
lean_inc(v_v_562_);
v___x_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_567_, 0, v_v_562_);
return v___x_567_;
}
default: 
{
v_t_559_ = v_r_564_;
goto _start;
}
}
}
else
{
lean_object* v___x_569_; 
v___x_569_ = lean_box(0);
return v___x_569_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg___boxed(lean_object* v_t_570_, lean_object* v_k_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_570_, v_k_571_);
lean_dec(v_k_571_);
lean_dec(v_t_570_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object* v_name_573_, lean_object* v_self_574_){
_start:
{
lean_object* v_targetDeclMap_575_; lean_object* v___x_576_; 
v_targetDeclMap_575_ = lean_ctor_get(v_self_574_, 14);
v___x_576_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_targetDeclMap_575_, v_name_573_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f___boxed(lean_object* v_name_577_, lean_object* v_self_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lake_Package_findTargetDecl_x3f(v_name_577_, v_self_578_);
lean_dec_ref(v_self_578_);
lean_dec(v_name_577_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(lean_object* v_00_u03b2_580_, lean_object* v_inst_581_, lean_object* v_t_582_, lean_object* v_k_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_582_, v_k_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___boxed(lean_object* v_00_u03b2_585_, lean_object* v_inst_586_, lean_object* v_t_587_, lean_object* v_k_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(v_00_u03b2_585_, v_inst_586_, v_t_587_, v_k_588_);
lean_dec(v_k_588_);
lean_dec(v_t_587_);
return v_res_589_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(lean_object* v_mod_593_, lean_object* v_as_594_, size_t v_i_595_, size_t v_stop_596_){
_start:
{
uint8_t v___x_597_; 
v___x_597_ = lean_usize_dec_eq(v_i_595_, v_stop_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v_kind_599_; lean_object* v_config_600_; uint8_t v___x_601_; uint8_t v___y_603_; lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_598_ = lean_array_uget_borrowed(v_as_594_, v_i_595_);
v_kind_599_ = lean_ctor_get(v___x_598_, 2);
v_config_600_ = lean_ctor_get(v___x_598_, 3);
v___x_601_ = 1;
v___x_607_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1));
v___x_608_ = lean_name_eq(v_kind_599_, v___x_607_);
if (v___x_608_ == 0)
{
v___y_603_ = v___x_597_;
goto v___jp_602_;
}
else
{
uint8_t v___x_609_; 
v___x_609_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_593_, v_config_600_);
v___y_603_ = v___x_609_;
goto v___jp_602_;
}
v___jp_602_:
{
if (v___y_603_ == 0)
{
size_t v___x_604_; size_t v___x_605_; 
v___x_604_ = ((size_t)1ULL);
v___x_605_ = lean_usize_add(v_i_595_, v___x_604_);
v_i_595_ = v___x_605_;
goto _start;
}
else
{
return v___x_601_;
}
}
}
else
{
uint8_t v___x_610_; 
v___x_610_ = 0;
return v___x_610_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___boxed(lean_object* v_mod_611_, lean_object* v_as_612_, lean_object* v_i_613_, lean_object* v_stop_614_){
_start:
{
size_t v_i_boxed_615_; size_t v_stop_boxed_616_; uint8_t v_res_617_; lean_object* v_r_618_; 
v_i_boxed_615_ = lean_unbox_usize(v_i_613_);
lean_dec(v_i_613_);
v_stop_boxed_616_ = lean_unbox_usize(v_stop_614_);
lean_dec(v_stop_614_);
v_res_617_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_611_, v_as_612_, v_i_boxed_615_, v_stop_boxed_616_);
lean_dec_ref(v_as_612_);
lean_dec(v_mod_611_);
v_r_618_ = lean_box(v_res_617_);
return v_r_618_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isLocalModule(lean_object* v_mod_619_, lean_object* v_self_620_){
_start:
{
lean_object* v_targetDecls_621_; lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v_targetDecls_621_ = lean_ctor_get(v_self_620_, 13);
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = lean_array_get_size(v_targetDecls_621_);
v___x_624_ = lean_nat_dec_lt(v___x_622_, v___x_623_);
if (v___x_624_ == 0)
{
return v___x_624_;
}
else
{
if (v___x_624_ == 0)
{
return v___x_624_;
}
else
{
size_t v___x_625_; size_t v___x_626_; uint8_t v___x_627_; 
v___x_625_ = ((size_t)0ULL);
v___x_626_ = lean_usize_of_nat(v___x_623_);
v___x_627_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_619_, v_targetDecls_621_, v___x_625_, v___x_626_);
return v___x_627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isLocalModule___boxed(lean_object* v_mod_628_, lean_object* v_self_629_){
_start:
{
uint8_t v_res_630_; lean_object* v_r_631_; 
v_res_630_ = l_Lake_Package_isLocalModule(v_mod_628_, v_self_629_);
lean_dec_ref(v_self_629_);
lean_dec(v_mod_628_);
v_r_631_ = lean_box(v_res_630_);
return v_r_631_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(lean_object* v_mod_632_, lean_object* v_as_633_, size_t v_i_634_, size_t v_stop_635_){
_start:
{
uint8_t v___x_636_; 
v___x_636_ = lean_usize_dec_eq(v_i_634_, v_stop_635_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; lean_object* v_kind_638_; lean_object* v_config_639_; uint8_t v___x_640_; uint8_t v___y_642_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_637_ = lean_array_uget_borrowed(v_as_633_, v_i_634_);
v_kind_638_ = lean_ctor_get(v___x_637_, 2);
v_config_639_ = lean_ctor_get(v___x_637_, 3);
v___x_640_ = 1;
v___x_653_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1));
v___x_654_ = lean_name_eq(v_kind_638_, v___x_653_);
if (v___x_654_ == 0)
{
goto v___jp_646_;
}
else
{
uint8_t v___x_655_; 
v___x_655_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_632_, v_config_639_);
if (v___x_655_ == 0)
{
goto v___jp_646_;
}
else
{
v___y_642_ = v___x_655_;
goto v___jp_641_;
}
}
v___jp_641_:
{
if (v___y_642_ == 0)
{
size_t v___x_643_; size_t v___x_644_; 
v___x_643_ = ((size_t)1ULL);
v___x_644_ = lean_usize_add(v_i_634_, v___x_643_);
v_i_634_ = v___x_644_;
goto _start;
}
else
{
return v___x_640_;
}
}
v___jp_646_:
{
lean_object* v_kind_647_; lean_object* v_config_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v_kind_647_ = lean_ctor_get(v___x_637_, 2);
v_config_648_ = lean_ctor_get(v___x_637_, 3);
v___x_649_ = l_Lake_LeanExe_keyword;
v___x_650_ = lean_name_eq(v_kind_647_, v___x_649_);
if (v___x_650_ == 0)
{
v___y_642_ = v___x_636_;
goto v___jp_641_;
}
else
{
lean_object* v_root_651_; uint8_t v___x_652_; 
v_root_651_ = lean_ctor_get(v_config_648_, 2);
v___x_652_ = lean_name_eq(v_root_651_, v_mod_632_);
v___y_642_ = v___x_652_;
goto v___jp_641_;
}
}
}
else
{
uint8_t v___x_656_; 
v___x_656_ = 0;
return v___x_656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0___boxed(lean_object* v_mod_657_, lean_object* v_as_658_, lean_object* v_i_659_, lean_object* v_stop_660_){
_start:
{
size_t v_i_boxed_661_; size_t v_stop_boxed_662_; uint8_t v_res_663_; lean_object* v_r_664_; 
v_i_boxed_661_ = lean_unbox_usize(v_i_659_);
lean_dec(v_i_659_);
v_stop_boxed_662_ = lean_unbox_usize(v_stop_660_);
lean_dec(v_stop_660_);
v_res_663_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_657_, v_as_658_, v_i_boxed_661_, v_stop_boxed_662_);
lean_dec_ref(v_as_658_);
lean_dec(v_mod_657_);
v_r_664_ = lean_box(v_res_663_);
return v_r_664_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isBuildableModule(lean_object* v_mod_665_, lean_object* v_self_666_){
_start:
{
lean_object* v_targetDecls_667_; lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v_targetDecls_667_ = lean_ctor_get(v_self_666_, 13);
v___x_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = lean_array_get_size(v_targetDecls_667_);
v___x_670_ = lean_nat_dec_lt(v___x_668_, v___x_669_);
if (v___x_670_ == 0)
{
return v___x_670_;
}
else
{
if (v___x_670_ == 0)
{
return v___x_670_;
}
else
{
size_t v___x_671_; size_t v___x_672_; uint8_t v___x_673_; 
v___x_671_ = ((size_t)0ULL);
v___x_672_ = lean_usize_of_nat(v___x_669_);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_665_, v_targetDecls_667_, v___x_671_, v___x_672_);
return v___x_673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isBuildableModule___boxed(lean_object* v_mod_674_, lean_object* v_self_675_){
_start:
{
uint8_t v_res_676_; lean_object* v_r_677_; 
v_res_676_ = l_Lake_Package_isBuildableModule(v_mod_674_, v_self_675_);
lean_dec_ref(v_self_675_);
lean_dec(v_mod_674_);
v_r_677_ = lean_box(v_res_676_);
return v_r_677_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_clean(lean_object* v_self_678_){
_start:
{
lean_object* v_config_680_; lean_object* v_dir_681_; lean_object* v_buildDir_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v_config_680_ = lean_ctor_get(v_self_678_, 6);
lean_inc_ref(v_config_680_);
v_dir_681_ = lean_ctor_get(v_self_678_, 4);
lean_inc_ref(v_dir_681_);
lean_dec_ref(v_self_678_);
v_buildDir_682_ = lean_ctor_get(v_config_680_, 5);
lean_inc_ref(v_buildDir_682_);
lean_dec_ref(v_config_680_);
v___x_683_ = l_System_FilePath_normalize(v_buildDir_682_);
v___x_684_ = l_Lake_joinRelative(v_dir_681_, v___x_683_);
v___x_685_ = l_Lake_removeDirAllIfExists(v___x_684_);
lean_dec_ref(v___x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_clean___boxed(lean_object* v_self_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lake_Package_clean(v_self_686_);
return v_res_688_;
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
