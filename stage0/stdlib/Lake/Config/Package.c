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
v_bootstrap_153_ = lean_ctor_get_uint8(v_config_152_, sizeof(void*)*27);
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
v_bootstrap_159_ = lean_ctor_get_uint8(v_config_158_, sizeof(void*)*27);
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
v_version_166_ = lean_ctor_get(v_config_165_, 17);
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
v_versionTags_171_ = lean_ctor_get(v_config_170_, 18);
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
v_description_176_ = lean_ctor_get(v_config_175_, 19);
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
v_keywords_181_ = lean_ctor_get(v_config_180_, 20);
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
v_homepage_186_ = lean_ctor_get(v_config_185_, 21);
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
v_reservoir_191_ = lean_ctor_get_uint8(v_config_190_, sizeof(void*)*27 + 3);
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
v_license_197_ = lean_ctor_get(v_config_196_, 22);
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
v_licenseFiles_222_ = lean_ctor_get(v_config_221_, 23);
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
v_licenseFiles_235_ = lean_ctor_get(v_config_233_, 23);
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
v_readmeFile_246_ = lean_ctor_get(v_config_245_, 24);
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
v_readmeFile_251_ = lean_ctor_get(v_config_249_, 24);
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
v_buildDir_279_ = lean_ctor_get(v_config_277_, 6);
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
v_testDriverArgs_284_ = lean_ctor_get(v_config_283_, 14);
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
v_lintDriverArgs_289_ = lean_ctor_get(v_config_288_, 16);
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
v_extraDepTargets_294_ = lean_ctor_get(v_config_293_, 3);
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
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f(lean_object* v_self_318_){
_start:
{
lean_object* v_config_319_; lean_object* v_releaseRepo_320_; 
v_config_319_ = lean_ctor_get(v_self_318_, 6);
v_releaseRepo_320_ = lean_ctor_get(v_config_319_, 11);
lean_inc(v_releaseRepo_320_);
return v_releaseRepo_320_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f___boxed(lean_object* v_self_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lake_Package_releaseRepo_x3f(v_self_321_);
lean_dec_ref(v_self_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f(lean_object* v_self_323_){
_start:
{
lean_object* v_remoteUrl_324_; lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v_remoteUrl_324_ = lean_ctor_get(v_self_323_, 11);
v___x_325_ = lean_string_utf8_byte_size(v_remoteUrl_324_);
v___x_326_ = lean_unsigned_to_nat(0u);
v___x_327_ = lean_nat_dec_eq(v___x_325_, v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; 
v___x_328_ = lean_box(0);
return v___x_328_;
}
else
{
lean_object* v___x_329_; 
lean_inc_ref(v_remoteUrl_324_);
v___x_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_329_, 0, v_remoteUrl_324_);
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f___boxed(lean_object* v_self_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lake_Package_remoteUrl_x3f(v_self_330_);
lean_dec_ref(v_self_330_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildArchiveFile(lean_object* v_self_332_){
_start:
{
lean_object* v_dir_333_; lean_object* v_buildArchive_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_dir_333_ = lean_ctor_get(v_self_332_, 4);
lean_inc_ref(v_dir_333_);
v_buildArchive_334_ = lean_ctor_get(v_self_332_, 19);
lean_inc_ref(v_buildArchive_334_);
lean_dec_ref(v_self_332_);
v___x_335_ = l_Lake_defaultLakeDir;
v___x_336_ = l_Lake_joinRelative(v_dir_333_, v___x_335_);
v___x_337_ = l_Lake_joinRelative(v___x_336_, v_buildArchive_334_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFile(lean_object* v_self_339_){
_start:
{
lean_object* v_dir_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_dir_340_ = lean_ctor_get(v_self_339_, 4);
lean_inc_ref(v_dir_340_);
lean_dec_ref(v_self_339_);
v___x_341_ = l_Lake_defaultLakeDir;
v___x_342_ = l_Lake_joinRelative(v_dir_340_, v___x_341_);
v___x_343_ = ((lean_object*)(l_Lake_Package_barrelFile___closed__0));
v___x_344_ = l_Lake_joinRelative(v___x_342_, v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_preferReleaseBuild(lean_object* v_self_345_){
_start:
{
lean_object* v_config_346_; uint8_t v_preferReleaseBuild_347_; 
v_config_346_ = lean_ctor_get(v_self_345_, 6);
v_preferReleaseBuild_347_ = lean_ctor_get_uint8(v_config_346_, sizeof(void*)*27 + 2);
return v_preferReleaseBuild_347_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_preferReleaseBuild___boxed(lean_object* v_self_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Lake_Package_preferReleaseBuild(v_self_348_);
lean_dec_ref(v_self_348_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_precompileModules(lean_object* v_self_351_){
_start:
{
lean_object* v_config_352_; uint8_t v_precompileModules_353_; 
v_config_352_ = lean_ctor_get(v_self_351_, 6);
v_precompileModules_353_ = lean_ctor_get_uint8(v_config_352_, sizeof(void*)*27 + 1);
return v_precompileModules_353_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_precompileModules___boxed(lean_object* v_self_354_){
_start:
{
uint8_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l_Lake_Package_precompileModules(v_self_354_);
lean_dec_ref(v_self_354_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs(lean_object* v_self_357_){
_start:
{
lean_object* v_config_358_; lean_object* v_moreGlobalServerArgs_359_; 
v_config_358_ = lean_ctor_get(v_self_357_, 6);
v_moreGlobalServerArgs_359_ = lean_ctor_get(v_config_358_, 4);
lean_inc_ref(v_moreGlobalServerArgs_359_);
return v_moreGlobalServerArgs_359_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs___boxed(lean_object* v_self_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lake_Package_moreGlobalServerArgs(v_self_360_);
lean_dec_ref(v_self_360_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions(lean_object* v_self_362_){
_start:
{
lean_object* v_config_363_; lean_object* v_toLeanConfig_364_; lean_object* v_leanOptions_365_; lean_object* v_moreServerOptions_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_config_363_ = lean_ctor_get(v_self_362_, 6);
v_toLeanConfig_364_ = lean_ctor_get(v_config_363_, 1);
v_leanOptions_365_ = lean_ctor_get(v_toLeanConfig_364_, 0);
v_moreServerOptions_366_ = lean_ctor_get(v_toLeanConfig_364_, 4);
v___x_367_ = l_Lean_LeanOptions_ofArray(v_leanOptions_365_);
v___x_368_ = l_Lean_LeanOptions_appendArray(v___x_367_, v_moreServerOptions_366_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions___boxed(lean_object* v_self_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lake_Package_moreServerOptions(v_self_369_);
lean_dec_ref(v_self_369_);
return v_res_370_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_buildType(lean_object* v_self_371_){
_start:
{
lean_object* v_config_372_; lean_object* v_toLeanConfig_373_; uint8_t v_buildType_374_; 
v_config_372_ = lean_ctor_get(v_self_371_, 6);
v_toLeanConfig_373_ = lean_ctor_get(v_config_372_, 1);
v_buildType_374_ = lean_ctor_get_uint8(v_toLeanConfig_373_, sizeof(void*)*13);
return v_buildType_374_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildType___boxed(lean_object* v_self_375_){
_start:
{
uint8_t v_res_376_; lean_object* v_r_377_; 
v_res_376_ = l_Lake_Package_buildType(v_self_375_);
lean_dec_ref(v_self_375_);
v_r_377_ = lean_box(v_res_376_);
return v_r_377_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_backend(lean_object* v_self_378_){
_start:
{
lean_object* v_config_379_; lean_object* v_toLeanConfig_380_; uint8_t v_backend_381_; 
v_config_379_ = lean_ctor_get(v_self_378_, 6);
v_toLeanConfig_380_ = lean_ctor_get(v_config_379_, 1);
v_backend_381_ = lean_ctor_get_uint8(v_toLeanConfig_380_, sizeof(void*)*13 + 1);
return v_backend_381_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_backend___boxed(lean_object* v_self_382_){
_start:
{
uint8_t v_res_383_; lean_object* v_r_384_; 
v_res_383_ = l_Lake_Package_backend(v_self_382_);
lean_dec_ref(v_self_382_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_allowImportAll(lean_object* v_self_385_){
_start:
{
lean_object* v_config_386_; uint8_t v_allowImportAll_387_; 
v_config_386_ = lean_ctor_get(v_self_385_, 6);
v_allowImportAll_387_ = lean_ctor_get_uint8(v_config_386_, sizeof(void*)*27 + 5);
return v_allowImportAll_387_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_allowImportAll___boxed(lean_object* v_self_388_){
_start:
{
uint8_t v_res_389_; lean_object* v_r_390_; 
v_res_389_ = l_Lake_Package_allowImportAll(v_self_388_);
lean_dec_ref(v_self_388_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs(lean_object* v_self_391_){
_start:
{
lean_object* v_config_392_; lean_object* v_toLeanConfig_393_; lean_object* v_dynlibs_394_; 
v_config_392_ = lean_ctor_get(v_self_391_, 6);
v_toLeanConfig_393_ = lean_ctor_get(v_config_392_, 1);
v_dynlibs_394_ = lean_ctor_get(v_toLeanConfig_393_, 11);
lean_inc_ref(v_dynlibs_394_);
return v_dynlibs_394_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs___boxed(lean_object* v_self_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lake_Package_dynlibs(v_self_395_);
lean_dec_ref(v_self_395_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins(lean_object* v_self_397_){
_start:
{
lean_object* v_config_398_; lean_object* v_toLeanConfig_399_; lean_object* v_plugins_400_; 
v_config_398_ = lean_ctor_get(v_self_397_, 6);
v_toLeanConfig_399_ = lean_ctor_get(v_config_398_, 1);
v_plugins_400_ = lean_ctor_get(v_toLeanConfig_399_, 12);
lean_inc_ref(v_plugins_400_);
return v_plugins_400_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins___boxed(lean_object* v_self_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lake_Package_plugins(v_self_401_);
lean_dec_ref(v_self_401_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions(lean_object* v_self_403_){
_start:
{
lean_object* v_config_404_; lean_object* v_toLeanConfig_405_; lean_object* v_leanOptions_406_; lean_object* v___x_407_; 
v_config_404_ = lean_ctor_get(v_self_403_, 6);
v_toLeanConfig_405_ = lean_ctor_get(v_config_404_, 1);
v_leanOptions_406_ = lean_ctor_get(v_toLeanConfig_405_, 0);
v___x_407_ = l_Lean_LeanOptions_ofArray(v_leanOptions_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions___boxed(lean_object* v_self_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lake_Package_leanOptions(v_self_408_);
lean_dec_ref(v_self_408_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs(lean_object* v_self_410_){
_start:
{
lean_object* v_config_411_; lean_object* v_toLeanConfig_412_; lean_object* v_moreLeanArgs_413_; 
v_config_411_ = lean_ctor_get(v_self_410_, 6);
v_toLeanConfig_412_ = lean_ctor_get(v_config_411_, 1);
v_moreLeanArgs_413_ = lean_ctor_get(v_toLeanConfig_412_, 1);
lean_inc_ref(v_moreLeanArgs_413_);
return v_moreLeanArgs_413_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs___boxed(lean_object* v_self_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lake_Package_moreLeanArgs(v_self_414_);
lean_dec_ref(v_self_414_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs(lean_object* v_self_416_){
_start:
{
lean_object* v_config_417_; lean_object* v_toLeanConfig_418_; lean_object* v_weakLeanArgs_419_; 
v_config_417_ = lean_ctor_get(v_self_416_, 6);
v_toLeanConfig_418_ = lean_ctor_get(v_config_417_, 1);
v_weakLeanArgs_419_ = lean_ctor_get(v_toLeanConfig_418_, 2);
lean_inc_ref(v_weakLeanArgs_419_);
return v_weakLeanArgs_419_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs___boxed(lean_object* v_self_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lake_Package_weakLeanArgs(v_self_420_);
lean_dec_ref(v_self_420_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs(lean_object* v_self_422_){
_start:
{
lean_object* v_config_423_; lean_object* v_toLeanConfig_424_; lean_object* v_moreLeancArgs_425_; 
v_config_423_ = lean_ctor_get(v_self_422_, 6);
v_toLeanConfig_424_ = lean_ctor_get(v_config_423_, 1);
v_moreLeancArgs_425_ = lean_ctor_get(v_toLeanConfig_424_, 3);
lean_inc_ref(v_moreLeancArgs_425_);
return v_moreLeancArgs_425_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs___boxed(lean_object* v_self_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lake_Package_moreLeancArgs(v_self_426_);
lean_dec_ref(v_self_426_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs(lean_object* v_self_428_){
_start:
{
lean_object* v_config_429_; lean_object* v_toLeanConfig_430_; lean_object* v_weakLeancArgs_431_; 
v_config_429_ = lean_ctor_get(v_self_428_, 6);
v_toLeanConfig_430_ = lean_ctor_get(v_config_429_, 1);
v_weakLeancArgs_431_ = lean_ctor_get(v_toLeanConfig_430_, 5);
lean_inc_ref(v_weakLeancArgs_431_);
return v_weakLeancArgs_431_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs___boxed(lean_object* v_self_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lake_Package_weakLeancArgs(v_self_432_);
lean_dec_ref(v_self_432_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs(lean_object* v_self_434_){
_start:
{
lean_object* v_config_435_; lean_object* v_toLeanConfig_436_; lean_object* v_moreLinkObjs_437_; 
v_config_435_ = lean_ctor_get(v_self_434_, 6);
v_toLeanConfig_436_ = lean_ctor_get(v_config_435_, 1);
v_moreLinkObjs_437_ = lean_ctor_get(v_toLeanConfig_436_, 6);
lean_inc_ref(v_moreLinkObjs_437_);
return v_moreLinkObjs_437_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs___boxed(lean_object* v_self_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lake_Package_moreLinkObjs(v_self_438_);
lean_dec_ref(v_self_438_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs(lean_object* v_self_440_){
_start:
{
lean_object* v_config_441_; lean_object* v_toLeanConfig_442_; lean_object* v_moreLinkLibs_443_; 
v_config_441_ = lean_ctor_get(v_self_440_, 6);
v_toLeanConfig_442_ = lean_ctor_get(v_config_441_, 1);
v_moreLinkLibs_443_ = lean_ctor_get(v_toLeanConfig_442_, 7);
lean_inc_ref(v_moreLinkLibs_443_);
return v_moreLinkLibs_443_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs___boxed(lean_object* v_self_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lake_Package_moreLinkLibs(v_self_444_);
lean_dec_ref(v_self_444_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs(lean_object* v_self_446_){
_start:
{
lean_object* v_config_447_; lean_object* v_toLeanConfig_448_; lean_object* v_moreLinkArgs_449_; 
v_config_447_ = lean_ctor_get(v_self_446_, 6);
v_toLeanConfig_448_ = lean_ctor_get(v_config_447_, 1);
v_moreLinkArgs_449_ = lean_ctor_get(v_toLeanConfig_448_, 8);
lean_inc_ref(v_moreLinkArgs_449_);
return v_moreLinkArgs_449_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs___boxed(lean_object* v_self_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lake_Package_moreLinkArgs(v_self_450_);
lean_dec_ref(v_self_450_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs(lean_object* v_self_452_){
_start:
{
lean_object* v_config_453_; lean_object* v_toLeanConfig_454_; lean_object* v_weakLinkArgs_455_; 
v_config_453_ = lean_ctor_get(v_self_452_, 6);
v_toLeanConfig_454_ = lean_ctor_get(v_config_453_, 1);
v_weakLinkArgs_455_ = lean_ctor_get(v_toLeanConfig_454_, 9);
lean_inc_ref(v_weakLinkArgs_455_);
return v_weakLinkArgs_455_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs___boxed(lean_object* v_self_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lake_Package_weakLinkArgs(v_self_456_);
lean_dec_ref(v_self_456_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_srcDir(lean_object* v_self_458_){
_start:
{
lean_object* v_config_459_; lean_object* v_dir_460_; lean_object* v_srcDir_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v_config_459_ = lean_ctor_get(v_self_458_, 6);
lean_inc_ref(v_config_459_);
v_dir_460_ = lean_ctor_get(v_self_458_, 4);
lean_inc_ref(v_dir_460_);
lean_dec_ref(v_self_458_);
v_srcDir_461_ = lean_ctor_get(v_config_459_, 5);
lean_inc_ref(v_srcDir_461_);
lean_dec_ref(v_config_459_);
v___x_462_ = l_System_FilePath_normalize(v_srcDir_461_);
v___x_463_ = l_Lake_joinRelative(v_dir_460_, v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_rootDir(lean_object* v_self_464_){
_start:
{
lean_object* v_config_465_; lean_object* v_dir_466_; lean_object* v_srcDir_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v_config_465_ = lean_ctor_get(v_self_464_, 6);
lean_inc_ref(v_config_465_);
v_dir_466_ = lean_ctor_get(v_self_464_, 4);
lean_inc_ref(v_dir_466_);
lean_dec_ref(v_self_464_);
v_srcDir_467_ = lean_ctor_get(v_config_465_, 5);
lean_inc_ref(v_srcDir_467_);
lean_dec_ref(v_config_465_);
v___x_468_ = l_System_FilePath_normalize(v_srcDir_467_);
v___x_469_ = l_Lake_joinRelative(v_dir_466_, v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanLibDir(lean_object* v_self_470_){
_start:
{
lean_object* v_config_471_; lean_object* v_dir_472_; lean_object* v_buildDir_473_; lean_object* v_leanLibDir_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_config_471_ = lean_ctor_get(v_self_470_, 6);
lean_inc_ref(v_config_471_);
v_dir_472_ = lean_ctor_get(v_self_470_, 4);
lean_inc_ref(v_dir_472_);
lean_dec_ref(v_self_470_);
v_buildDir_473_ = lean_ctor_get(v_config_471_, 6);
lean_inc_ref(v_buildDir_473_);
v_leanLibDir_474_ = lean_ctor_get(v_config_471_, 7);
lean_inc_ref(v_leanLibDir_474_);
lean_dec_ref(v_config_471_);
v___x_475_ = l_System_FilePath_normalize(v_buildDir_473_);
v___x_476_ = l_Lake_joinRelative(v_dir_472_, v___x_475_);
v___x_477_ = l_System_FilePath_normalize(v_leanLibDir_474_);
v___x_478_ = l_Lake_joinRelative(v___x_476_, v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_staticLibDir(lean_object* v_self_479_){
_start:
{
lean_object* v_config_480_; lean_object* v_dir_481_; lean_object* v_buildDir_482_; lean_object* v_nativeLibDir_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v_config_480_ = lean_ctor_get(v_self_479_, 6);
lean_inc_ref(v_config_480_);
v_dir_481_ = lean_ctor_get(v_self_479_, 4);
lean_inc_ref(v_dir_481_);
lean_dec_ref(v_self_479_);
v_buildDir_482_ = lean_ctor_get(v_config_480_, 6);
lean_inc_ref(v_buildDir_482_);
v_nativeLibDir_483_ = lean_ctor_get(v_config_480_, 8);
lean_inc_ref(v_nativeLibDir_483_);
lean_dec_ref(v_config_480_);
v___x_484_ = l_System_FilePath_normalize(v_buildDir_482_);
v___x_485_ = l_Lake_joinRelative(v_dir_481_, v___x_484_);
v___x_486_ = l_System_FilePath_normalize(v_nativeLibDir_483_);
v___x_487_ = l_Lake_joinRelative(v___x_485_, v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_sharedLibDir(lean_object* v_self_488_){
_start:
{
lean_object* v_config_489_; lean_object* v_dir_490_; lean_object* v_buildDir_491_; lean_object* v_nativeLibDir_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v_config_489_ = lean_ctor_get(v_self_488_, 6);
lean_inc_ref(v_config_489_);
v_dir_490_ = lean_ctor_get(v_self_488_, 4);
lean_inc_ref(v_dir_490_);
lean_dec_ref(v_self_488_);
v_buildDir_491_ = lean_ctor_get(v_config_489_, 6);
lean_inc_ref(v_buildDir_491_);
v_nativeLibDir_492_ = lean_ctor_get(v_config_489_, 8);
lean_inc_ref(v_nativeLibDir_492_);
lean_dec_ref(v_config_489_);
v___x_493_ = l_System_FilePath_normalize(v_buildDir_491_);
v___x_494_ = l_Lake_joinRelative(v_dir_490_, v___x_493_);
v___x_495_ = l_System_FilePath_normalize(v_nativeLibDir_492_);
v___x_496_ = l_Lake_joinRelative(v___x_494_, v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_binDir(lean_object* v_self_497_){
_start:
{
lean_object* v_config_498_; lean_object* v_dir_499_; lean_object* v_buildDir_500_; lean_object* v_binDir_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_config_498_ = lean_ctor_get(v_self_497_, 6);
lean_inc_ref(v_config_498_);
v_dir_499_ = lean_ctor_get(v_self_497_, 4);
lean_inc_ref(v_dir_499_);
lean_dec_ref(v_self_497_);
v_buildDir_500_ = lean_ctor_get(v_config_498_, 6);
lean_inc_ref(v_buildDir_500_);
v_binDir_501_ = lean_ctor_get(v_config_498_, 9);
lean_inc_ref(v_binDir_501_);
lean_dec_ref(v_config_498_);
v___x_502_ = l_System_FilePath_normalize(v_buildDir_500_);
v___x_503_ = l_Lake_joinRelative(v_dir_499_, v___x_502_);
v___x_504_ = l_System_FilePath_normalize(v_binDir_501_);
v___x_505_ = l_Lake_joinRelative(v___x_503_, v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_irDir(lean_object* v_self_506_){
_start:
{
lean_object* v_config_507_; lean_object* v_dir_508_; lean_object* v_buildDir_509_; lean_object* v_irDir_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v_config_507_ = lean_ctor_get(v_self_506_, 6);
lean_inc_ref(v_config_507_);
v_dir_508_ = lean_ctor_get(v_self_506_, 4);
lean_inc_ref(v_dir_508_);
lean_dec_ref(v_self_506_);
v_buildDir_509_ = lean_ctor_get(v_config_507_, 6);
lean_inc_ref(v_buildDir_509_);
v_irDir_510_ = lean_ctor_get(v_config_507_, 10);
lean_inc_ref(v_irDir_510_);
lean_dec_ref(v_config_507_);
v___x_511_ = l_System_FilePath_normalize(v_buildDir_509_);
v___x_512_ = l_Lake_joinRelative(v_dir_508_, v___x_511_);
v___x_513_ = l_System_FilePath_normalize(v_irDir_510_);
v___x_514_ = l_Lake_joinRelative(v___x_512_, v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_libPrefixOnWindows(lean_object* v_self_515_){
_start:
{
lean_object* v_config_516_; uint8_t v_libPrefixOnWindows_517_; 
v_config_516_ = lean_ctor_get(v_self_515_, 6);
v_libPrefixOnWindows_517_ = lean_ctor_get_uint8(v_config_516_, sizeof(void*)*27 + 4);
return v_libPrefixOnWindows_517_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_libPrefixOnWindows___boxed(lean_object* v_self_518_){
_start:
{
uint8_t v_res_519_; lean_object* v_r_520_; 
v_res_519_ = l_Lake_Package_libPrefixOnWindows(v_self_518_);
lean_dec_ref(v_self_518_);
v_r_520_ = lean_box(v_res_519_);
return v_r_520_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f(lean_object* v_self_521_){
_start:
{
lean_object* v_config_522_; lean_object* v_enableArtifactCache_x3f_523_; 
v_config_522_ = lean_ctor_get(v_self_521_, 6);
v_enableArtifactCache_x3f_523_ = lean_ctor_get(v_config_522_, 25);
lean_inc(v_enableArtifactCache_x3f_523_);
return v_enableArtifactCache_x3f_523_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f___boxed(lean_object* v_self_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lake_Package_enableArtifactCache_x3f(v_self_524_);
lean_dec_ref(v_self_524_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f(lean_object* v_self_526_){
_start:
{
lean_object* v_config_527_; lean_object* v_restoreAllArtifacts_x3f_528_; 
v_config_527_ = lean_ctor_get(v_self_526_, 6);
v_restoreAllArtifacts_x3f_528_ = lean_ctor_get(v_config_527_, 26);
lean_inc(v_restoreAllArtifacts_x3f_528_);
return v_restoreAllArtifacts_x3f_528_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f___boxed(lean_object* v_self_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lake_Package_restoreAllArtifacts_x3f(v_self_529_);
lean_dec_ref(v_self_529_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_cacheScope(lean_object* v_self_531_){
_start:
{
lean_object* v_baseName_532_; uint8_t v___x_533_; lean_object* v___x_534_; 
v_baseName_532_ = lean_ctor_get(v_self_531_, 1);
lean_inc(v_baseName_532_);
lean_dec_ref(v_self_531_);
v___x_533_ = 0;
v___x_534_ = l_Lean_Name_toString(v_baseName_532_, v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(lean_object* v_self_536_){
_start:
{
lean_object* v_origName_537_; lean_object* v_scope_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_origName_537_ = lean_ctor_get(v_self_536_, 3);
lean_inc(v_origName_537_);
v_scope_538_ = lean_ctor_get(v_self_536_, 10);
lean_inc_ref(v_scope_538_);
lean_dec_ref(v_self_536_);
v___x_539_ = ((lean_object*)(l___private_Lake_Config_Package_0__Lake_Package_reservoirScope___closed__0));
v___x_540_ = lean_string_append(v_scope_538_, v___x_539_);
v___x_541_ = 0;
v___x_542_ = l_Lean_Name_toString(v_origName_537_, v___x_541_);
v___x_543_ = lean_string_append(v___x_540_, v___x_542_);
lean_dec_ref(v___x_542_);
v___x_544_ = l_Lake_CacheServiceScope_ofString(v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirScope_x3f(lean_object* v_self_545_){
_start:
{
lean_object* v_scope_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v_scope_546_ = lean_ctor_get(v_self_545_, 10);
v___x_547_ = lean_string_utf8_byte_size(v_scope_546_);
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = lean_nat_dec_eq(v___x_547_, v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(v_self_545_);
v___x_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
else
{
lean_object* v___x_552_; 
lean_dec_ref(v_self_545_);
v___x_552_ = lean_box(0);
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(lean_object* v_t_553_, lean_object* v_k_554_){
_start:
{
if (lean_obj_tag(v_t_553_) == 0)
{
lean_object* v_k_555_; lean_object* v_v_556_; lean_object* v_l_557_; lean_object* v_r_558_; uint8_t v___x_559_; 
v_k_555_ = lean_ctor_get(v_t_553_, 1);
v_v_556_ = lean_ctor_get(v_t_553_, 2);
v_l_557_ = lean_ctor_get(v_t_553_, 3);
v_r_558_ = lean_ctor_get(v_t_553_, 4);
v___x_559_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_554_, v_k_555_);
switch(v___x_559_)
{
case 0:
{
v_t_553_ = v_l_557_;
goto _start;
}
case 1:
{
lean_object* v___x_561_; 
lean_inc(v_v_556_);
v___x_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_561_, 0, v_v_556_);
return v___x_561_;
}
default: 
{
v_t_553_ = v_r_558_;
goto _start;
}
}
}
else
{
lean_object* v___x_563_; 
v___x_563_ = lean_box(0);
return v___x_563_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg___boxed(lean_object* v_t_564_, lean_object* v_k_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_564_, v_k_565_);
lean_dec(v_k_565_);
lean_dec(v_t_564_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object* v_name_567_, lean_object* v_self_568_){
_start:
{
lean_object* v_targetDeclMap_569_; lean_object* v___x_570_; 
v_targetDeclMap_569_ = lean_ctor_get(v_self_568_, 14);
v___x_570_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_targetDeclMap_569_, v_name_567_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f___boxed(lean_object* v_name_571_, lean_object* v_self_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lake_Package_findTargetDecl_x3f(v_name_571_, v_self_572_);
lean_dec_ref(v_self_572_);
lean_dec(v_name_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(lean_object* v_00_u03b2_574_, lean_object* v_inst_575_, lean_object* v_t_576_, lean_object* v_k_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_576_, v_k_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___boxed(lean_object* v_00_u03b2_579_, lean_object* v_inst_580_, lean_object* v_t_581_, lean_object* v_k_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(v_00_u03b2_579_, v_inst_580_, v_t_581_, v_k_582_);
lean_dec(v_k_582_);
lean_dec(v_t_581_);
return v_res_583_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(lean_object* v_mod_587_, lean_object* v_as_588_, size_t v_i_589_, size_t v_stop_590_){
_start:
{
uint8_t v___x_591_; 
v___x_591_ = lean_usize_dec_eq(v_i_589_, v_stop_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; lean_object* v_kind_593_; lean_object* v_config_594_; uint8_t v___x_595_; uint8_t v___y_597_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_592_ = lean_array_uget_borrowed(v_as_588_, v_i_589_);
v_kind_593_ = lean_ctor_get(v___x_592_, 2);
v_config_594_ = lean_ctor_get(v___x_592_, 3);
v___x_595_ = 1;
v___x_601_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1));
v___x_602_ = lean_name_eq(v_kind_593_, v___x_601_);
if (v___x_602_ == 0)
{
v___y_597_ = v___x_591_;
goto v___jp_596_;
}
else
{
uint8_t v___x_603_; 
v___x_603_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_587_, v_config_594_);
v___y_597_ = v___x_603_;
goto v___jp_596_;
}
v___jp_596_:
{
if (v___y_597_ == 0)
{
size_t v___x_598_; size_t v___x_599_; 
v___x_598_ = ((size_t)1ULL);
v___x_599_ = lean_usize_add(v_i_589_, v___x_598_);
v_i_589_ = v___x_599_;
goto _start;
}
else
{
return v___x_595_;
}
}
}
else
{
uint8_t v___x_604_; 
v___x_604_ = 0;
return v___x_604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___boxed(lean_object* v_mod_605_, lean_object* v_as_606_, lean_object* v_i_607_, lean_object* v_stop_608_){
_start:
{
size_t v_i_boxed_609_; size_t v_stop_boxed_610_; uint8_t v_res_611_; lean_object* v_r_612_; 
v_i_boxed_609_ = lean_unbox_usize(v_i_607_);
lean_dec(v_i_607_);
v_stop_boxed_610_ = lean_unbox_usize(v_stop_608_);
lean_dec(v_stop_608_);
v_res_611_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_605_, v_as_606_, v_i_boxed_609_, v_stop_boxed_610_);
lean_dec_ref(v_as_606_);
lean_dec(v_mod_605_);
v_r_612_ = lean_box(v_res_611_);
return v_r_612_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isLocalModule(lean_object* v_mod_613_, lean_object* v_self_614_){
_start:
{
lean_object* v_targetDecls_615_; lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v_targetDecls_615_ = lean_ctor_get(v_self_614_, 13);
v___x_616_ = lean_unsigned_to_nat(0u);
v___x_617_ = lean_array_get_size(v_targetDecls_615_);
v___x_618_ = lean_nat_dec_lt(v___x_616_, v___x_617_);
if (v___x_618_ == 0)
{
return v___x_618_;
}
else
{
if (v___x_618_ == 0)
{
return v___x_618_;
}
else
{
size_t v___x_619_; size_t v___x_620_; uint8_t v___x_621_; 
v___x_619_ = ((size_t)0ULL);
v___x_620_ = lean_usize_of_nat(v___x_617_);
v___x_621_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_613_, v_targetDecls_615_, v___x_619_, v___x_620_);
return v___x_621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isLocalModule___boxed(lean_object* v_mod_622_, lean_object* v_self_623_){
_start:
{
uint8_t v_res_624_; lean_object* v_r_625_; 
v_res_624_ = l_Lake_Package_isLocalModule(v_mod_622_, v_self_623_);
lean_dec_ref(v_self_623_);
lean_dec(v_mod_622_);
v_r_625_ = lean_box(v_res_624_);
return v_r_625_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(lean_object* v_mod_626_, lean_object* v_as_627_, size_t v_i_628_, size_t v_stop_629_){
_start:
{
uint8_t v___x_630_; 
v___x_630_ = lean_usize_dec_eq(v_i_628_, v_stop_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v_kind_632_; lean_object* v_config_633_; uint8_t v___x_634_; uint8_t v___y_636_; lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_631_ = lean_array_uget_borrowed(v_as_627_, v_i_628_);
v_kind_632_ = lean_ctor_get(v___x_631_, 2);
v_config_633_ = lean_ctor_get(v___x_631_, 3);
v___x_634_ = 1;
v___x_647_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1));
v___x_648_ = lean_name_eq(v_kind_632_, v___x_647_);
if (v___x_648_ == 0)
{
goto v___jp_640_;
}
else
{
uint8_t v___x_649_; 
v___x_649_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_626_, v_config_633_);
if (v___x_649_ == 0)
{
goto v___jp_640_;
}
else
{
v___y_636_ = v___x_649_;
goto v___jp_635_;
}
}
v___jp_635_:
{
if (v___y_636_ == 0)
{
size_t v___x_637_; size_t v___x_638_; 
v___x_637_ = ((size_t)1ULL);
v___x_638_ = lean_usize_add(v_i_628_, v___x_637_);
v_i_628_ = v___x_638_;
goto _start;
}
else
{
return v___x_634_;
}
}
v___jp_640_:
{
lean_object* v_kind_641_; lean_object* v_config_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v_kind_641_ = lean_ctor_get(v___x_631_, 2);
v_config_642_ = lean_ctor_get(v___x_631_, 3);
v___x_643_ = l_Lake_LeanExe_keyword;
v___x_644_ = lean_name_eq(v_kind_641_, v___x_643_);
if (v___x_644_ == 0)
{
v___y_636_ = v___x_630_;
goto v___jp_635_;
}
else
{
lean_object* v_root_645_; uint8_t v___x_646_; 
v_root_645_ = lean_ctor_get(v_config_642_, 2);
v___x_646_ = lean_name_eq(v_root_645_, v_mod_626_);
v___y_636_ = v___x_646_;
goto v___jp_635_;
}
}
}
else
{
uint8_t v___x_650_; 
v___x_650_ = 0;
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0___boxed(lean_object* v_mod_651_, lean_object* v_as_652_, lean_object* v_i_653_, lean_object* v_stop_654_){
_start:
{
size_t v_i_boxed_655_; size_t v_stop_boxed_656_; uint8_t v_res_657_; lean_object* v_r_658_; 
v_i_boxed_655_ = lean_unbox_usize(v_i_653_);
lean_dec(v_i_653_);
v_stop_boxed_656_ = lean_unbox_usize(v_stop_654_);
lean_dec(v_stop_654_);
v_res_657_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_651_, v_as_652_, v_i_boxed_655_, v_stop_boxed_656_);
lean_dec_ref(v_as_652_);
lean_dec(v_mod_651_);
v_r_658_ = lean_box(v_res_657_);
return v_r_658_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isBuildableModule(lean_object* v_mod_659_, lean_object* v_self_660_){
_start:
{
lean_object* v_targetDecls_661_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v_targetDecls_661_ = lean_ctor_get(v_self_660_, 13);
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = lean_array_get_size(v_targetDecls_661_);
v___x_664_ = lean_nat_dec_lt(v___x_662_, v___x_663_);
if (v___x_664_ == 0)
{
return v___x_664_;
}
else
{
if (v___x_664_ == 0)
{
return v___x_664_;
}
else
{
size_t v___x_665_; size_t v___x_666_; uint8_t v___x_667_; 
v___x_665_ = ((size_t)0ULL);
v___x_666_ = lean_usize_of_nat(v___x_663_);
v___x_667_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_659_, v_targetDecls_661_, v___x_665_, v___x_666_);
return v___x_667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isBuildableModule___boxed(lean_object* v_mod_668_, lean_object* v_self_669_){
_start:
{
uint8_t v_res_670_; lean_object* v_r_671_; 
v_res_670_ = l_Lake_Package_isBuildableModule(v_mod_668_, v_self_669_);
lean_dec_ref(v_self_669_);
lean_dec(v_mod_668_);
v_r_671_ = lean_box(v_res_670_);
return v_r_671_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_clean(lean_object* v_self_672_){
_start:
{
lean_object* v_config_674_; lean_object* v_dir_675_; lean_object* v_buildDir_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_config_674_ = lean_ctor_get(v_self_672_, 6);
lean_inc_ref(v_config_674_);
v_dir_675_ = lean_ctor_get(v_self_672_, 4);
lean_inc_ref(v_dir_675_);
lean_dec_ref(v_self_672_);
v_buildDir_676_ = lean_ctor_get(v_config_674_, 6);
lean_inc_ref(v_buildDir_676_);
lean_dec_ref(v_config_674_);
v___x_677_ = l_System_FilePath_normalize(v_buildDir_676_);
v___x_678_ = l_Lake_joinRelative(v_dir_675_, v___x_677_);
v___x_679_ = l_Lake_removeDirAllIfExists(v___x_678_);
lean_dec_ref(v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_clean___boxed(lean_object* v_self_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lake_Package_clean(v_self_680_);
return v_res_682_;
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
