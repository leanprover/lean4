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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
static const lean_string_object l_Lake_instInhabitedPackage_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedPackage_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedPackage_default___closed__0_value;
static lean_once_cell_t l_Lake_instInhabitedPackage_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPackage_default___closed__1;
static const lean_array_object l_Lake_instInhabitedPackage_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instInhabitedPackage_default___closed__2 = (const lean_object*)&l_Lake_instInhabitedPackage_default___closed__2_value;
static const lean_array_object l_Lake_instInhabitedPackage_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instInhabitedPackage_default___closed__3 = (const lean_object*)&l_Lake_instInhabitedPackage_default___closed__3_value;
static lean_once_cell_t l_Lake_instInhabitedPackage_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedPackage_default___closed__4;
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
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__1(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = lean_box(0);
v___x_7_ = l_Lake_instInhabitedPackageConfig_default(v___x_6_, v___x_6_);
return v___x_7_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default___closed__4(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_12_ = lean_box(1);
v___x_13_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__3));
v___x_14_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__2));
v___x_15_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__1, &l_Lake_instInhabitedPackage_default___closed__1_once, _init_l_Lake_instInhabitedPackage_default___closed__1);
v___x_16_ = ((lean_object*)(l_Lake_instInhabitedPackage_default___closed__0));
v___x_17_ = lean_box(0);
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = lean_alloc_ctor(0, 22, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___x_17_);
lean_ctor_set(v___x_19_, 2, v___x_17_);
lean_ctor_set(v___x_19_, 3, v___x_17_);
lean_ctor_set(v___x_19_, 4, v___x_16_);
lean_ctor_set(v___x_19_, 5, v___x_16_);
lean_ctor_set(v___x_19_, 6, v___x_15_);
lean_ctor_set(v___x_19_, 7, v___x_16_);
lean_ctor_set(v___x_19_, 8, v___x_16_);
lean_ctor_set(v___x_19_, 9, v___x_16_);
lean_ctor_set(v___x_19_, 10, v___x_16_);
lean_ctor_set(v___x_19_, 11, v___x_16_);
lean_ctor_set(v___x_19_, 12, v___x_14_);
lean_ctor_set(v___x_19_, 13, v___x_13_);
lean_ctor_set(v___x_19_, 14, v___x_12_);
lean_ctor_set(v___x_19_, 15, v___x_14_);
lean_ctor_set(v___x_19_, 16, v___x_12_);
lean_ctor_set(v___x_19_, 17, v___x_14_);
lean_ctor_set(v___x_19_, 18, v___x_13_);
lean_ctor_set(v___x_19_, 19, v___x_16_);
lean_ctor_set(v___x_19_, 20, v___x_16_);
lean_ctor_set(v___x_19_, 21, v___x_16_);
return v___x_19_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage_default(void){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_obj_once(&l_Lake_instInhabitedPackage_default___closed__4, &l_Lake_instInhabitedPackage_default___closed__4_once, _init_l_Lake_instInhabitedPackage_default___closed__4);
return v___x_20_;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage(void){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lake_instInhabitedPackage_default;
return v___x_21_;
}
}
static uint64_t _init_l_Lake_Package_instHashable___lam__0___closed__0(void){
_start:
{
lean_object* v___x_22_; uint64_t v___x_23_; 
v___x_22_ = lean_unsigned_to_nat(1723u);
v___x_23_ = lean_uint64_of_nat(v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT uint64_t l_Lake_Package_instHashable___lam__0(lean_object* v_pkg_24_){
_start:
{
lean_object* v_keyName_25_; 
v_keyName_25_ = lean_ctor_get(v_pkg_24_, 2);
if (lean_obj_tag(v_keyName_25_) == 0)
{
uint64_t v___x_26_; 
v___x_26_ = lean_uint64_once(&l_Lake_Package_instHashable___lam__0___closed__0, &l_Lake_Package_instHashable___lam__0___closed__0_once, _init_l_Lake_Package_instHashable___lam__0___closed__0);
return v___x_26_;
}
else
{
uint64_t v_hash_27_; 
v_hash_27_ = lean_ctor_get_uint64(v_keyName_25_, sizeof(void*)*2);
return v_hash_27_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instHashable___lam__0___boxed(lean_object* v_pkg_28_){
_start:
{
uint64_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = l_Lake_Package_instHashable___lam__0(v_pkg_28_);
lean_dec_ref(v_pkg_28_);
v_r_30_ = lean_box_uint64(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_instBEq___lam__0(lean_object* v_p1_33_, lean_object* v_p2_34_){
_start:
{
lean_object* v_wsIdx_35_; lean_object* v_wsIdx_36_; uint8_t v___x_37_; 
v_wsIdx_35_ = lean_ctor_get(v_p1_33_, 0);
v_wsIdx_36_ = lean_ctor_get(v_p2_34_, 0);
v___x_37_ = lean_nat_dec_eq(v_wsIdx_35_, v_wsIdx_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instBEq___lam__0___boxed(lean_object* v_p1_38_, lean_object* v_p2_39_){
_start:
{
uint8_t v_res_40_; lean_object* v_r_41_; 
v_res_40_ = l_Lake_Package_instBEq___lam__0(v_p1_38_, v_p2_39_);
lean_dec_ref(v_p2_39_);
lean_dec_ref(v_p1_38_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_prettyName(lean_object* v_self_44_){
_start:
{
lean_object* v_baseName_45_; uint8_t v___x_46_; lean_object* v___x_47_; 
v_baseName_45_ = lean_ctor_get(v_self_44_, 1);
lean_inc(v_baseName_45_);
lean_dec_ref(v_self_44_);
v___x_46_ = 0;
v___x_47_ = l_Lean_Name_toString(v_baseName_45_, v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instQueryJson___lam__0(lean_object* v_x_48_){
_start:
{
lean_object* v_keyName_49_; uint8_t v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_keyName_49_ = lean_ctor_get(v_x_48_, 2);
lean_inc(v_keyName_49_);
lean_dec_ref(v_x_48_);
v___x_50_ = 1;
v___x_51_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_keyName_49_, v___x_50_);
v___x_52_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_instQueryText___lam__0(lean_object* v_x_55_){
_start:
{
lean_object* v_baseName_56_; uint8_t v___x_57_; lean_object* v___x_58_; 
v_baseName_56_ = lean_ctor_get(v_x_55_, 1);
lean_inc(v_baseName_56_);
lean_dec_ref(v_x_55_);
v___x_57_ = 0;
v___x_58_ = l_Lean_Name_toString(v_baseName_56_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_name(lean_object* v_self_61_){
_start:
{
lean_object* v_baseName_62_; 
v_baseName_62_ = lean_ctor_get(v_self_61_, 1);
lean_inc(v_baseName_62_);
return v_baseName_62_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_name___boxed(lean_object* v_self_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lake_Package_name(v_self_63_);
lean_dec_ref(v_self_63_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirName(lean_object* v_self_65_){
_start:
{
lean_object* v_origName_66_; uint8_t v___x_67_; lean_object* v___x_68_; 
v_origName_66_ = lean_ctor_get(v_self_65_, 3);
lean_inc(v_origName_66_);
lean_dec_ref(v_self_65_);
v___x_67_ = 0;
v___x_68_ = l_Lean_Name_toString(v_origName_66_, v___x_67_);
return v___x_68_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty___closed__0(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = lean_box(0);
v___x_70_ = lean_unsigned_to_nat(16u);
v___x_71_ = lean_mk_array(v___x_70_, v___x_69_);
return v___x_71_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty___closed__1(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_obj_once(&l_Lake_PackageSet_empty___closed__0, &l_Lake_PackageSet_empty___closed__0_once, _init_l_Lake_PackageSet_empty___closed__0);
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v___x_72_);
return v___x_74_;
}
}
static lean_object* _init_l_Lake_PackageSet_empty(void){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_obj_once(&l_Lake_PackageSet_empty___closed__1, &l_Lake_PackageSet_empty___closed__1_once, _init_l_Lake_PackageSet_empty___closed__1);
return v___x_75_;
}
}
static lean_object* _init_l_Lake_OrdPackageSet_empty___closed__0(void){
_start:
{
lean_object* v___f_76_; lean_object* v___f_77_; lean_object* v___x_78_; 
v___f_76_ = ((lean_object*)(l_Lake_Package_instBEq___closed__0));
v___f_77_ = ((lean_object*)(l_Lake_Package_instHashable___closed__0));
v___x_78_ = l_Lake_OrdHashSet_empty(lean_box(0), v___f_77_, v___f_76_);
return v___x_78_;
}
}
static lean_object* _init_l_Lake_OrdPackageSet_empty(void){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_obj_once(&l_Lake_OrdPackageSet_empty___closed__0, &l_Lake_OrdPackageSet_empty___closed__0_once, _init_l_Lake_OrdPackageSet_empty___closed__0);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___lam__0(lean_object* v_self_80_){
_start:
{
lean_inc_ref(v_self_80_);
return v_self_80_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___lam__0___boxed(lean_object* v_self_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lake_NPackage_instCoeOutPackage___lam__0(v_self_81_);
lean_dec_ref(v_self_81_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage(lean_object* v_n_84_){
_start:
{
lean_object* v___f_85_; 
v___f_85_ = ((lean_object*)(l_Lake_NPackage_instCoeOutPackage___closed__0));
return v___f_85_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeOutPackage___boxed(lean_object* v_n_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lake_NPackage_instCoeOutPackage(v_n_86_);
lean_dec(v_n_86_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeDepPackageKeyName(lean_object* v_pkg_88_){
_start:
{
lean_inc_ref(v_pkg_88_);
return v_pkg_88_;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_instCoeDepPackageKeyName___boxed(lean_object* v_pkg_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lake_NPackage_instCoeDepPackageKeyName(v_pkg_89_);
lean_dec_ref(v_pkg_89_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___lam__0(lean_object* v_x_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_box(0);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v___y_93_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___lam__0___boxed(lean_object* v_x_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lake_instInhabitedPostUpdateHook_default___lam__0(v_x_97_, v___y_98_, v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v_x_97_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default(lean_object* v_pkgName_103_){
_start:
{
lean_object* v___f_104_; 
v___f_104_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___closed__0));
return v___f_104_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook_default___boxed(lean_object* v_pkgName_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lake_instInhabitedPostUpdateHook_default(v_pkgName_105_);
lean_dec(v_pkgName_105_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook(lean_object* v_a_107_){
_start:
{
lean_object* v___f_108_; 
v___f_108_ = ((lean_object*)(l_Lake_instInhabitedPostUpdateHook_default___closed__0));
return v___f_108_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___boxed(lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lake_instInhabitedPostUpdateHook(v_a_109_);
lean_dec(v_a_109_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(lean_object* v_a_111_){
_start:
{
lean_inc_ref(v_a_111_);
return v_a_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg___boxed(lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(v_a_112_);
lean_dec_ref(v_a_112_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(lean_object* v_name_114_, lean_object* v_a_115_){
_start:
{
lean_inc_ref(v_a_115_);
return v_a_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed(lean_object* v_name_116_, lean_object* v_a_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(v_name_116_, v_a_117_);
lean_dec_ref(v_a_117_);
lean_dec(v_name_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeMk(lean_object* v_name_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_alloc_closure((void*)(l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed), 2, 1);
lean_closure_set(v___x_120_, 0, v_name_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(lean_object* v_a_121_){
_start:
{
lean_inc(v_a_121_);
return v_a_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg___boxed(lean_object* v_a_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(v_a_122_);
lean_dec(v_a_122_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(lean_object* v_name_124_, lean_object* v_a_125_){
_start:
{
lean_inc(v_a_125_);
return v_a_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed(lean_object* v_name_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(v_name_126_, v_a_127_);
lean_dec(v_a_127_);
lean_dec(v_name_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeGet(lean_object* v_name_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = lean_alloc_closure((void*)(l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed), 2, 1);
lean_closure_set(v___x_130_, 0, v_name_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(lean_object* v_inst_131_){
_start:
{
lean_inc_ref(v_inst_131_);
return v_inst_131_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg___boxed(lean_object* v_inst_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(v_inst_132_);
lean_dec_ref(v_inst_132_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(lean_object* v_name_134_, lean_object* v_inst_135_){
_start:
{
lean_inc_ref(v_inst_135_);
return v_inst_135_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___boxed(lean_object* v_name_136_, lean_object* v_inst_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(v_name_136_, v_inst_137_);
lean_dec_ref(v_inst_137_);
lean_dec(v_name_136_);
return v_res_138_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isRoot(lean_object* v_self_146_){
_start:
{
lean_object* v_wsIdx_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v_wsIdx_147_ = lean_ctor_get(v_self_146_, 0);
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = lean_nat_dec_eq(v_wsIdx_147_, v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isRoot___boxed(lean_object* v_self_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l_Lake_Package_isRoot(v_self_150_);
lean_dec_ref(v_self_150_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_bootstrap(lean_object* v_self_153_){
_start:
{
lean_object* v_config_154_; uint8_t v_bootstrap_155_; 
v_config_154_ = lean_ctor_get(v_self_153_, 6);
v_bootstrap_155_ = lean_ctor_get_uint8(v_config_154_, sizeof(void*)*26);
return v_bootstrap_155_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_bootstrap___boxed(lean_object* v_self_156_){
_start:
{
uint8_t v_res_157_; lean_object* v_r_158_; 
v_res_157_ = l_Lake_Package_bootstrap(v_self_156_);
lean_dec_ref(v_self_156_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_id_x3f(lean_object* v_self_159_){
_start:
{
lean_object* v_config_160_; uint8_t v_bootstrap_161_; 
v_config_160_ = lean_ctor_get(v_self_159_, 6);
v_bootstrap_161_ = lean_ctor_get_uint8(v_config_160_, sizeof(void*)*26);
if (v_bootstrap_161_ == 0)
{
lean_object* v_origName_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_origName_162_ = lean_ctor_get(v_self_159_, 3);
lean_inc(v_origName_162_);
lean_dec_ref(v_self_159_);
v___x_163_ = l_Lean_Name_toString(v_origName_162_, v_bootstrap_161_);
v___x_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
else
{
lean_object* v___x_165_; 
lean_dec_ref(v_self_159_);
v___x_165_ = lean_box(0);
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_version(lean_object* v_self_166_){
_start:
{
lean_object* v_config_167_; lean_object* v_version_168_; 
v_config_167_ = lean_ctor_get(v_self_166_, 6);
v_version_168_ = lean_ctor_get(v_config_167_, 16);
lean_inc_ref(v_version_168_);
return v_version_168_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_version___boxed(lean_object* v_self_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lake_Package_version(v_self_169_);
lean_dec_ref(v_self_169_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_versionTags(lean_object* v_self_171_){
_start:
{
lean_object* v_config_172_; lean_object* v_versionTags_173_; 
v_config_172_ = lean_ctor_get(v_self_171_, 6);
v_versionTags_173_ = lean_ctor_get(v_config_172_, 17);
lean_inc_ref(v_versionTags_173_);
return v_versionTags_173_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_versionTags___boxed(lean_object* v_self_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lake_Package_versionTags(v_self_174_);
lean_dec_ref(v_self_174_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_description(lean_object* v_self_176_){
_start:
{
lean_object* v_config_177_; lean_object* v_description_178_; 
v_config_177_ = lean_ctor_get(v_self_176_, 6);
v_description_178_ = lean_ctor_get(v_config_177_, 18);
lean_inc_ref(v_description_178_);
return v_description_178_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_description___boxed(lean_object* v_self_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lake_Package_description(v_self_179_);
lean_dec_ref(v_self_179_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_keywords(lean_object* v_self_181_){
_start:
{
lean_object* v_config_182_; lean_object* v_keywords_183_; 
v_config_182_ = lean_ctor_get(v_self_181_, 6);
v_keywords_183_ = lean_ctor_get(v_config_182_, 19);
lean_inc_ref(v_keywords_183_);
return v_keywords_183_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_keywords___boxed(lean_object* v_self_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lake_Package_keywords(v_self_184_);
lean_dec_ref(v_self_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_homepage(lean_object* v_self_186_){
_start:
{
lean_object* v_config_187_; lean_object* v_homepage_188_; 
v_config_187_ = lean_ctor_get(v_self_186_, 6);
v_homepage_188_ = lean_ctor_get(v_config_187_, 20);
lean_inc_ref(v_homepage_188_);
return v_homepage_188_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_homepage___boxed(lean_object* v_self_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lake_Package_homepage(v_self_189_);
lean_dec_ref(v_self_189_);
return v_res_190_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_reservoir(lean_object* v_self_191_){
_start:
{
lean_object* v_config_192_; uint8_t v_reservoir_193_; 
v_config_192_ = lean_ctor_get(v_self_191_, 6);
v_reservoir_193_ = lean_ctor_get_uint8(v_config_192_, sizeof(void*)*26 + 3);
return v_reservoir_193_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoir___boxed(lean_object* v_self_194_){
_start:
{
uint8_t v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l_Lake_Package_reservoir(v_self_194_);
lean_dec_ref(v_self_194_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_license(lean_object* v_self_197_){
_start:
{
lean_object* v_config_198_; lean_object* v_license_199_; 
v_config_198_ = lean_ctor_get(v_self_197_, 6);
v_license_199_ = lean_ctor_get(v_config_198_, 21);
lean_inc_ref(v_license_199_);
return v_license_199_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_license___boxed(lean_object* v_self_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lake_Package_license(v_self_200_);
lean_dec_ref(v_self_200_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLicenseFiles(lean_object* v_self_222_){
_start:
{
lean_object* v_config_223_; lean_object* v_licenseFiles_224_; lean_object* v___f_225_; lean_object* v___x_226_; size_t v_sz_227_; size_t v___x_228_; lean_object* v___x_229_; 
v_config_223_ = lean_ctor_get(v_self_222_, 6);
lean_inc_ref(v_config_223_);
lean_dec_ref(v_self_222_);
v_licenseFiles_224_ = lean_ctor_get(v_config_223_, 22);
lean_inc_ref(v_licenseFiles_224_);
lean_dec_ref(v_config_223_);
v___f_225_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__0));
v___x_226_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__10));
v_sz_227_ = lean_array_size(v_licenseFiles_224_);
v___x_228_ = ((size_t)0ULL);
v___x_229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_226_, v___f_225_, v_sz_227_, v___x_228_, v_licenseFiles_224_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles___lam__0(lean_object* v_dir_230_, lean_object* v_x_231_){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = l_System_FilePath_normalize(v_x_231_);
v___x_233_ = l_Lake_joinRelative(v_dir_230_, v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles(lean_object* v_self_234_){
_start:
{
lean_object* v_config_235_; lean_object* v_dir_236_; lean_object* v_licenseFiles_237_; lean_object* v___f_238_; lean_object* v___f_239_; lean_object* v___x_240_; size_t v_sz_241_; size_t v___x_242_; lean_object* v___x_243_; size_t v_sz_244_; lean_object* v___x_245_; 
v_config_235_ = lean_ctor_get(v_self_234_, 6);
lean_inc_ref(v_config_235_);
v_dir_236_ = lean_ctor_get(v_self_234_, 4);
lean_inc_ref(v_dir_236_);
lean_dec_ref(v_self_234_);
v_licenseFiles_237_ = lean_ctor_get(v_config_235_, 22);
lean_inc_ref(v_licenseFiles_237_);
lean_dec_ref(v_config_235_);
v___f_238_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__0));
v___f_239_ = lean_alloc_closure((void*)(l_Lake_Package_licenseFiles___lam__0), 2, 1);
lean_closure_set(v___f_239_, 0, v_dir_236_);
v___x_240_ = ((lean_object*)(l_Lake_Package_relLicenseFiles___closed__10));
v_sz_241_ = lean_array_size(v_licenseFiles_237_);
v___x_242_ = ((size_t)0ULL);
v___x_243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_240_, v___f_238_, v_sz_241_, v___x_242_, v_licenseFiles_237_);
v_sz_244_ = lean_array_size(v___x_243_);
v___x_245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_240_, v___f_239_, v_sz_244_, v___x_242_, v___x_243_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relReadmeFile(lean_object* v_self_246_){
_start:
{
lean_object* v_config_247_; lean_object* v_readmeFile_248_; lean_object* v___x_249_; 
v_config_247_ = lean_ctor_get(v_self_246_, 6);
lean_inc_ref(v_config_247_);
lean_dec_ref(v_self_246_);
v_readmeFile_248_ = lean_ctor_get(v_config_247_, 23);
lean_inc_ref(v_readmeFile_248_);
lean_dec_ref(v_config_247_);
v___x_249_ = l_System_FilePath_normalize(v_readmeFile_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_readmeFile(lean_object* v_self_250_){
_start:
{
lean_object* v_config_251_; lean_object* v_dir_252_; lean_object* v_readmeFile_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v_config_251_ = lean_ctor_get(v_self_250_, 6);
lean_inc_ref(v_config_251_);
v_dir_252_ = lean_ctor_get(v_self_250_, 4);
lean_inc_ref(v_dir_252_);
lean_dec_ref(v_self_250_);
v_readmeFile_253_ = lean_ctor_get(v_config_251_, 23);
lean_inc_ref(v_readmeFile_253_);
lean_dec_ref(v_config_251_);
v___x_254_ = l_System_FilePath_normalize(v_readmeFile_253_);
v___x_255_ = l_Lake_joinRelative(v_dir_252_, v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir(lean_object* v_x_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lake_defaultLakeDir;
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___boxed(lean_object* v_x_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lake_Package_relLakeDir(v_x_258_);
lean_dec_ref(v_x_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lakeDir(lean_object* v_self_260_){
_start:
{
lean_object* v_dir_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_dir_261_ = lean_ctor_get(v_self_260_, 4);
lean_inc_ref(v_dir_261_);
lean_dec_ref(v_self_260_);
v___x_262_ = l_Lake_defaultLakeDir;
v___x_263_ = l_Lake_joinRelative(v_dir_261_, v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relPkgsDir(lean_object* v_self_264_){
_start:
{
lean_object* v_config_265_; lean_object* v_toWorkspaceConfig_266_; lean_object* v___x_267_; 
v_config_265_ = lean_ctor_get(v_self_264_, 6);
lean_inc_ref(v_config_265_);
lean_dec_ref(v_self_264_);
v_toWorkspaceConfig_266_ = lean_ctor_get(v_config_265_, 0);
lean_inc_ref(v_toWorkspaceConfig_266_);
lean_dec_ref(v_config_265_);
v___x_267_ = l_System_FilePath_normalize(v_toWorkspaceConfig_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_pkgsDir(lean_object* v_self_268_){
_start:
{
lean_object* v_config_269_; lean_object* v_dir_270_; lean_object* v_toWorkspaceConfig_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_config_269_ = lean_ctor_get(v_self_268_, 6);
lean_inc_ref(v_config_269_);
v_dir_270_ = lean_ctor_get(v_self_268_, 4);
lean_inc_ref(v_dir_270_);
lean_dec_ref(v_self_268_);
v_toWorkspaceConfig_271_ = lean_ctor_get(v_config_269_, 0);
lean_inc_ref(v_toWorkspaceConfig_271_);
lean_dec_ref(v_config_269_);
v___x_272_ = l_System_FilePath_normalize(v_toWorkspaceConfig_271_);
v___x_273_ = l_Lake_joinRelative(v_dir_270_, v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_manifestFile(lean_object* v_self_274_){
_start:
{
lean_object* v_dir_275_; lean_object* v_relManifestFile_276_; lean_object* v___x_277_; 
v_dir_275_ = lean_ctor_get(v_self_274_, 4);
lean_inc_ref(v_dir_275_);
v_relManifestFile_276_ = lean_ctor_get(v_self_274_, 9);
lean_inc_ref(v_relManifestFile_276_);
lean_dec_ref(v_self_274_);
v___x_277_ = l_Lake_joinRelative(v_dir_275_, v_relManifestFile_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildDir(lean_object* v_self_278_){
_start:
{
lean_object* v_config_279_; lean_object* v_dir_280_; lean_object* v_buildDir_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_config_279_ = lean_ctor_get(v_self_278_, 6);
lean_inc_ref(v_config_279_);
v_dir_280_ = lean_ctor_get(v_self_278_, 4);
lean_inc_ref(v_dir_280_);
lean_dec_ref(v_self_278_);
v_buildDir_281_ = lean_ctor_get(v_config_279_, 5);
lean_inc_ref(v_buildDir_281_);
lean_dec_ref(v_config_279_);
v___x_282_ = l_System_FilePath_normalize(v_buildDir_281_);
v___x_283_ = l_Lake_joinRelative(v_dir_280_, v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs(lean_object* v_self_284_){
_start:
{
lean_object* v_config_285_; lean_object* v_testDriverArgs_286_; 
v_config_285_ = lean_ctor_get(v_self_284_, 6);
v_testDriverArgs_286_ = lean_ctor_get(v_config_285_, 13);
lean_inc_ref(v_testDriverArgs_286_);
return v_testDriverArgs_286_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs___boxed(lean_object* v_self_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lake_Package_testDriverArgs(v_self_287_);
lean_dec_ref(v_self_287_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs(lean_object* v_self_289_){
_start:
{
lean_object* v_config_290_; lean_object* v_lintDriverArgs_291_; 
v_config_290_ = lean_ctor_get(v_self_289_, 6);
v_lintDriverArgs_291_ = lean_ctor_get(v_config_290_, 15);
lean_inc_ref(v_lintDriverArgs_291_);
return v_lintDriverArgs_291_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs___boxed(lean_object* v_self_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lake_Package_lintDriverArgs(v_self_292_);
lean_dec_ref(v_self_292_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets(lean_object* v_self_294_){
_start:
{
lean_object* v_config_295_; lean_object* v_extraDepTargets_296_; 
v_config_295_ = lean_ctor_get(v_self_294_, 6);
v_extraDepTargets_296_ = lean_ctor_get(v_config_295_, 2);
lean_inc_ref(v_extraDepTargets_296_);
return v_extraDepTargets_296_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets___boxed(lean_object* v_self_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lake_Package_extraDepTargets(v_self_297_);
lean_dec_ref(v_self_297_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent(lean_object* v_self_299_){
_start:
{
lean_object* v_config_300_; lean_object* v_toLeanConfig_301_; lean_object* v_platformIndependent_302_; 
v_config_300_ = lean_ctor_get(v_self_299_, 6);
v_toLeanConfig_301_ = lean_ctor_get(v_config_300_, 1);
v_platformIndependent_302_ = lean_ctor_get(v_toLeanConfig_301_, 10);
lean_inc(v_platformIndependent_302_);
return v_platformIndependent_302_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent___boxed(lean_object* v_self_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lake_Package_platformIndependent(v_self_303_);
lean_dec_ref(v_self_303_);
return v_res_304_;
}
}
static lean_object* _init_l_Lake_Package_isPlatformIndependent___closed__0(void){
_start:
{
lean_object* v___x_305_; lean_object* v___f_306_; 
v___x_305_ = lean_alloc_closure((void*)(l_instDecidableEqBool___boxed), 2, 0);
v___f_306_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_306_, 0, v___x_305_);
return v___f_306_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isPlatformIndependent(lean_object* v_self_310_){
_start:
{
lean_object* v_config_311_; lean_object* v_toLeanConfig_312_; lean_object* v_platformIndependent_313_; lean_object* v___f_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v_config_311_ = lean_ctor_get(v_self_310_, 6);
lean_inc_ref(v_config_311_);
lean_dec_ref(v_self_310_);
v_toLeanConfig_312_ = lean_ctor_get(v_config_311_, 1);
lean_inc_ref(v_toLeanConfig_312_);
lean_dec_ref(v_config_311_);
v_platformIndependent_313_ = lean_ctor_get(v_toLeanConfig_312_, 10);
lean_inc(v_platformIndependent_313_);
lean_dec_ref(v_toLeanConfig_312_);
v___f_314_ = lean_obj_once(&l_Lake_Package_isPlatformIndependent___closed__0, &l_Lake_Package_isPlatformIndependent___closed__0_once, _init_l_Lake_Package_isPlatformIndependent___closed__0);
v___x_315_ = ((lean_object*)(l_Lake_Package_isPlatformIndependent___closed__1));
v___x_316_ = l_Option_instBEq_beq___redArg(v___f_314_, v_platformIndependent_313_, v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isPlatformIndependent___boxed(lean_object* v_self_317_){
_start:
{
uint8_t v_res_318_; lean_object* v_r_319_; 
v_res_318_ = l_Lake_Package_isPlatformIndependent(v_self_317_);
v_r_319_ = lean_box(v_res_318_);
return v_r_319_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_fixedToolchain(lean_object* v_self_320_){
_start:
{
lean_object* v_config_321_; uint8_t v_fixedToolchain_322_; 
v_config_321_ = lean_ctor_get(v_self_320_, 6);
v_fixedToolchain_322_ = lean_ctor_get_uint8(v_config_321_, sizeof(void*)*26 + 6);
return v_fixedToolchain_322_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_fixedToolchain___boxed(lean_object* v_self_323_){
_start:
{
uint8_t v_res_324_; lean_object* v_r_325_; 
v_res_324_ = l_Lake_Package_fixedToolchain(v_self_323_);
lean_dec_ref(v_self_323_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f(lean_object* v_self_326_){
_start:
{
lean_object* v_config_327_; lean_object* v_releaseRepo_328_; 
v_config_327_ = lean_ctor_get(v_self_326_, 6);
v_releaseRepo_328_ = lean_ctor_get(v_config_327_, 10);
lean_inc(v_releaseRepo_328_);
return v_releaseRepo_328_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f___boxed(lean_object* v_self_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lake_Package_releaseRepo_x3f(v_self_329_);
lean_dec_ref(v_self_329_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f(lean_object* v_self_331_){
_start:
{
lean_object* v_remoteUrl_332_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v_remoteUrl_332_ = lean_ctor_get(v_self_331_, 11);
v___x_333_ = lean_string_utf8_byte_size(v_remoteUrl_332_);
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_335_ = lean_nat_dec_eq(v___x_333_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; 
v___x_336_ = lean_box(0);
return v___x_336_;
}
else
{
lean_object* v___x_337_; 
lean_inc_ref(v_remoteUrl_332_);
v___x_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_337_, 0, v_remoteUrl_332_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f___boxed(lean_object* v_self_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lake_Package_remoteUrl_x3f(v_self_338_);
lean_dec_ref(v_self_338_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildArchiveFile(lean_object* v_self_340_){
_start:
{
lean_object* v_dir_341_; lean_object* v_buildArchive_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_dir_341_ = lean_ctor_get(v_self_340_, 4);
lean_inc_ref(v_dir_341_);
v_buildArchive_342_ = lean_ctor_get(v_self_340_, 19);
lean_inc_ref(v_buildArchive_342_);
lean_dec_ref(v_self_340_);
v___x_343_ = l_Lake_defaultLakeDir;
v___x_344_ = l_Lake_joinRelative(v_dir_341_, v___x_343_);
v___x_345_ = l_Lake_joinRelative(v___x_344_, v_buildArchive_342_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFile(lean_object* v_self_347_){
_start:
{
lean_object* v_dir_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_dir_348_ = lean_ctor_get(v_self_347_, 4);
lean_inc_ref(v_dir_348_);
lean_dec_ref(v_self_347_);
v___x_349_ = l_Lake_defaultLakeDir;
v___x_350_ = l_Lake_joinRelative(v_dir_348_, v___x_349_);
v___x_351_ = ((lean_object*)(l_Lake_Package_barrelFile___closed__0));
v___x_352_ = l_Lake_joinRelative(v___x_350_, v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_preferReleaseBuild(lean_object* v_self_353_){
_start:
{
lean_object* v_config_354_; uint8_t v_preferReleaseBuild_355_; 
v_config_354_ = lean_ctor_get(v_self_353_, 6);
v_preferReleaseBuild_355_ = lean_ctor_get_uint8(v_config_354_, sizeof(void*)*26 + 2);
return v_preferReleaseBuild_355_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_preferReleaseBuild___boxed(lean_object* v_self_356_){
_start:
{
uint8_t v_res_357_; lean_object* v_r_358_; 
v_res_357_ = l_Lake_Package_preferReleaseBuild(v_self_356_);
lean_dec_ref(v_self_356_);
v_r_358_ = lean_box(v_res_357_);
return v_r_358_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_precompileModules(lean_object* v_self_359_){
_start:
{
lean_object* v_config_360_; uint8_t v_precompileModules_361_; 
v_config_360_ = lean_ctor_get(v_self_359_, 6);
v_precompileModules_361_ = lean_ctor_get_uint8(v_config_360_, sizeof(void*)*26 + 1);
return v_precompileModules_361_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_precompileModules___boxed(lean_object* v_self_362_){
_start:
{
uint8_t v_res_363_; lean_object* v_r_364_; 
v_res_363_ = l_Lake_Package_precompileModules(v_self_362_);
lean_dec_ref(v_self_362_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs(lean_object* v_self_365_){
_start:
{
lean_object* v_config_366_; lean_object* v_moreGlobalServerArgs_367_; 
v_config_366_ = lean_ctor_get(v_self_365_, 6);
v_moreGlobalServerArgs_367_ = lean_ctor_get(v_config_366_, 3);
lean_inc_ref(v_moreGlobalServerArgs_367_);
return v_moreGlobalServerArgs_367_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs___boxed(lean_object* v_self_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lake_Package_moreGlobalServerArgs(v_self_368_);
lean_dec_ref(v_self_368_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions(lean_object* v_self_370_){
_start:
{
lean_object* v_config_371_; lean_object* v_toLeanConfig_372_; lean_object* v_leanOptions_373_; lean_object* v_moreServerOptions_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_config_371_ = lean_ctor_get(v_self_370_, 6);
v_toLeanConfig_372_ = lean_ctor_get(v_config_371_, 1);
v_leanOptions_373_ = lean_ctor_get(v_toLeanConfig_372_, 0);
v_moreServerOptions_374_ = lean_ctor_get(v_toLeanConfig_372_, 4);
v___x_375_ = l_Lean_LeanOptions_ofArray(v_leanOptions_373_);
v___x_376_ = l_Lean_LeanOptions_appendArray(v___x_375_, v_moreServerOptions_374_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions___boxed(lean_object* v_self_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lake_Package_moreServerOptions(v_self_377_);
lean_dec_ref(v_self_377_);
return v_res_378_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_buildType(lean_object* v_self_379_){
_start:
{
lean_object* v_config_380_; lean_object* v_toLeanConfig_381_; uint8_t v_buildType_382_; 
v_config_380_ = lean_ctor_get(v_self_379_, 6);
v_toLeanConfig_381_ = lean_ctor_get(v_config_380_, 1);
v_buildType_382_ = lean_ctor_get_uint8(v_toLeanConfig_381_, sizeof(void*)*13);
return v_buildType_382_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildType___boxed(lean_object* v_self_383_){
_start:
{
uint8_t v_res_384_; lean_object* v_r_385_; 
v_res_384_ = l_Lake_Package_buildType(v_self_383_);
lean_dec_ref(v_self_383_);
v_r_385_ = lean_box(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_backend(lean_object* v_self_386_){
_start:
{
lean_object* v_config_387_; lean_object* v_toLeanConfig_388_; uint8_t v_backend_389_; 
v_config_387_ = lean_ctor_get(v_self_386_, 6);
v_toLeanConfig_388_ = lean_ctor_get(v_config_387_, 1);
v_backend_389_ = lean_ctor_get_uint8(v_toLeanConfig_388_, sizeof(void*)*13 + 1);
return v_backend_389_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_backend___boxed(lean_object* v_self_390_){
_start:
{
uint8_t v_res_391_; lean_object* v_r_392_; 
v_res_391_ = l_Lake_Package_backend(v_self_390_);
lean_dec_ref(v_self_390_);
v_r_392_ = lean_box(v_res_391_);
return v_r_392_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_allowImportAll(lean_object* v_self_393_){
_start:
{
lean_object* v_config_394_; uint8_t v_allowImportAll_395_; 
v_config_394_ = lean_ctor_get(v_self_393_, 6);
v_allowImportAll_395_ = lean_ctor_get_uint8(v_config_394_, sizeof(void*)*26 + 5);
return v_allowImportAll_395_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_allowImportAll___boxed(lean_object* v_self_396_){
_start:
{
uint8_t v_res_397_; lean_object* v_r_398_; 
v_res_397_ = l_Lake_Package_allowImportAll(v_self_396_);
lean_dec_ref(v_self_396_);
v_r_398_ = lean_box(v_res_397_);
return v_r_398_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs(lean_object* v_self_399_){
_start:
{
lean_object* v_config_400_; lean_object* v_toLeanConfig_401_; lean_object* v_dynlibs_402_; 
v_config_400_ = lean_ctor_get(v_self_399_, 6);
v_toLeanConfig_401_ = lean_ctor_get(v_config_400_, 1);
v_dynlibs_402_ = lean_ctor_get(v_toLeanConfig_401_, 11);
lean_inc_ref(v_dynlibs_402_);
return v_dynlibs_402_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs___boxed(lean_object* v_self_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lake_Package_dynlibs(v_self_403_);
lean_dec_ref(v_self_403_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins(lean_object* v_self_405_){
_start:
{
lean_object* v_config_406_; lean_object* v_toLeanConfig_407_; lean_object* v_plugins_408_; 
v_config_406_ = lean_ctor_get(v_self_405_, 6);
v_toLeanConfig_407_ = lean_ctor_get(v_config_406_, 1);
v_plugins_408_ = lean_ctor_get(v_toLeanConfig_407_, 12);
lean_inc_ref(v_plugins_408_);
return v_plugins_408_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins___boxed(lean_object* v_self_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lake_Package_plugins(v_self_409_);
lean_dec_ref(v_self_409_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions(lean_object* v_self_411_){
_start:
{
lean_object* v_config_412_; lean_object* v_toLeanConfig_413_; lean_object* v_leanOptions_414_; lean_object* v___x_415_; 
v_config_412_ = lean_ctor_get(v_self_411_, 6);
v_toLeanConfig_413_ = lean_ctor_get(v_config_412_, 1);
v_leanOptions_414_ = lean_ctor_get(v_toLeanConfig_413_, 0);
v___x_415_ = l_Lean_LeanOptions_ofArray(v_leanOptions_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions___boxed(lean_object* v_self_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lake_Package_leanOptions(v_self_416_);
lean_dec_ref(v_self_416_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs(lean_object* v_self_418_){
_start:
{
lean_object* v_config_419_; lean_object* v_toLeanConfig_420_; lean_object* v_moreLeanArgs_421_; 
v_config_419_ = lean_ctor_get(v_self_418_, 6);
v_toLeanConfig_420_ = lean_ctor_get(v_config_419_, 1);
v_moreLeanArgs_421_ = lean_ctor_get(v_toLeanConfig_420_, 1);
lean_inc_ref(v_moreLeanArgs_421_);
return v_moreLeanArgs_421_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs___boxed(lean_object* v_self_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lake_Package_moreLeanArgs(v_self_422_);
lean_dec_ref(v_self_422_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs(lean_object* v_self_424_){
_start:
{
lean_object* v_config_425_; lean_object* v_toLeanConfig_426_; lean_object* v_weakLeanArgs_427_; 
v_config_425_ = lean_ctor_get(v_self_424_, 6);
v_toLeanConfig_426_ = lean_ctor_get(v_config_425_, 1);
v_weakLeanArgs_427_ = lean_ctor_get(v_toLeanConfig_426_, 2);
lean_inc_ref(v_weakLeanArgs_427_);
return v_weakLeanArgs_427_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs___boxed(lean_object* v_self_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lake_Package_weakLeanArgs(v_self_428_);
lean_dec_ref(v_self_428_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs(lean_object* v_self_430_){
_start:
{
lean_object* v_config_431_; lean_object* v_toLeanConfig_432_; lean_object* v_moreLeancArgs_433_; 
v_config_431_ = lean_ctor_get(v_self_430_, 6);
v_toLeanConfig_432_ = lean_ctor_get(v_config_431_, 1);
v_moreLeancArgs_433_ = lean_ctor_get(v_toLeanConfig_432_, 3);
lean_inc_ref(v_moreLeancArgs_433_);
return v_moreLeancArgs_433_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs___boxed(lean_object* v_self_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lake_Package_moreLeancArgs(v_self_434_);
lean_dec_ref(v_self_434_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs(lean_object* v_self_436_){
_start:
{
lean_object* v_config_437_; lean_object* v_toLeanConfig_438_; lean_object* v_weakLeancArgs_439_; 
v_config_437_ = lean_ctor_get(v_self_436_, 6);
v_toLeanConfig_438_ = lean_ctor_get(v_config_437_, 1);
v_weakLeancArgs_439_ = lean_ctor_get(v_toLeanConfig_438_, 5);
lean_inc_ref(v_weakLeancArgs_439_);
return v_weakLeancArgs_439_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs___boxed(lean_object* v_self_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lake_Package_weakLeancArgs(v_self_440_);
lean_dec_ref(v_self_440_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs(lean_object* v_self_442_){
_start:
{
lean_object* v_config_443_; lean_object* v_toLeanConfig_444_; lean_object* v_moreLinkObjs_445_; 
v_config_443_ = lean_ctor_get(v_self_442_, 6);
v_toLeanConfig_444_ = lean_ctor_get(v_config_443_, 1);
v_moreLinkObjs_445_ = lean_ctor_get(v_toLeanConfig_444_, 6);
lean_inc_ref(v_moreLinkObjs_445_);
return v_moreLinkObjs_445_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs___boxed(lean_object* v_self_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lake_Package_moreLinkObjs(v_self_446_);
lean_dec_ref(v_self_446_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs(lean_object* v_self_448_){
_start:
{
lean_object* v_config_449_; lean_object* v_toLeanConfig_450_; lean_object* v_moreLinkLibs_451_; 
v_config_449_ = lean_ctor_get(v_self_448_, 6);
v_toLeanConfig_450_ = lean_ctor_get(v_config_449_, 1);
v_moreLinkLibs_451_ = lean_ctor_get(v_toLeanConfig_450_, 7);
lean_inc_ref(v_moreLinkLibs_451_);
return v_moreLinkLibs_451_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs___boxed(lean_object* v_self_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lake_Package_moreLinkLibs(v_self_452_);
lean_dec_ref(v_self_452_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs(lean_object* v_self_454_){
_start:
{
lean_object* v_config_455_; lean_object* v_toLeanConfig_456_; lean_object* v_moreLinkArgs_457_; 
v_config_455_ = lean_ctor_get(v_self_454_, 6);
v_toLeanConfig_456_ = lean_ctor_get(v_config_455_, 1);
v_moreLinkArgs_457_ = lean_ctor_get(v_toLeanConfig_456_, 8);
lean_inc_ref(v_moreLinkArgs_457_);
return v_moreLinkArgs_457_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs___boxed(lean_object* v_self_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lake_Package_moreLinkArgs(v_self_458_);
lean_dec_ref(v_self_458_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs(lean_object* v_self_460_){
_start:
{
lean_object* v_config_461_; lean_object* v_toLeanConfig_462_; lean_object* v_weakLinkArgs_463_; 
v_config_461_ = lean_ctor_get(v_self_460_, 6);
v_toLeanConfig_462_ = lean_ctor_get(v_config_461_, 1);
v_weakLinkArgs_463_ = lean_ctor_get(v_toLeanConfig_462_, 9);
lean_inc_ref(v_weakLinkArgs_463_);
return v_weakLinkArgs_463_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs___boxed(lean_object* v_self_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lake_Package_weakLinkArgs(v_self_464_);
lean_dec_ref(v_self_464_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_srcDir(lean_object* v_self_466_){
_start:
{
lean_object* v_config_467_; lean_object* v_dir_468_; lean_object* v_srcDir_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_config_467_ = lean_ctor_get(v_self_466_, 6);
lean_inc_ref(v_config_467_);
v_dir_468_ = lean_ctor_get(v_self_466_, 4);
lean_inc_ref(v_dir_468_);
lean_dec_ref(v_self_466_);
v_srcDir_469_ = lean_ctor_get(v_config_467_, 4);
lean_inc_ref(v_srcDir_469_);
lean_dec_ref(v_config_467_);
v___x_470_ = l_System_FilePath_normalize(v_srcDir_469_);
v___x_471_ = l_Lake_joinRelative(v_dir_468_, v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_rootDir(lean_object* v_self_472_){
_start:
{
lean_object* v_config_473_; lean_object* v_dir_474_; lean_object* v_srcDir_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_config_473_ = lean_ctor_get(v_self_472_, 6);
lean_inc_ref(v_config_473_);
v_dir_474_ = lean_ctor_get(v_self_472_, 4);
lean_inc_ref(v_dir_474_);
lean_dec_ref(v_self_472_);
v_srcDir_475_ = lean_ctor_get(v_config_473_, 4);
lean_inc_ref(v_srcDir_475_);
lean_dec_ref(v_config_473_);
v___x_476_ = l_System_FilePath_normalize(v_srcDir_475_);
v___x_477_ = l_Lake_joinRelative(v_dir_474_, v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanLibDir(lean_object* v_self_478_){
_start:
{
lean_object* v_config_479_; lean_object* v_dir_480_; lean_object* v_buildDir_481_; lean_object* v_leanLibDir_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_config_479_ = lean_ctor_get(v_self_478_, 6);
lean_inc_ref(v_config_479_);
v_dir_480_ = lean_ctor_get(v_self_478_, 4);
lean_inc_ref(v_dir_480_);
lean_dec_ref(v_self_478_);
v_buildDir_481_ = lean_ctor_get(v_config_479_, 5);
lean_inc_ref(v_buildDir_481_);
v_leanLibDir_482_ = lean_ctor_get(v_config_479_, 6);
lean_inc_ref(v_leanLibDir_482_);
lean_dec_ref(v_config_479_);
v___x_483_ = l_System_FilePath_normalize(v_buildDir_481_);
v___x_484_ = l_Lake_joinRelative(v_dir_480_, v___x_483_);
v___x_485_ = l_System_FilePath_normalize(v_leanLibDir_482_);
v___x_486_ = l_Lake_joinRelative(v___x_484_, v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_staticLibDir(lean_object* v_self_487_){
_start:
{
lean_object* v_config_488_; lean_object* v_dir_489_; lean_object* v_buildDir_490_; lean_object* v_nativeLibDir_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_config_488_ = lean_ctor_get(v_self_487_, 6);
lean_inc_ref(v_config_488_);
v_dir_489_ = lean_ctor_get(v_self_487_, 4);
lean_inc_ref(v_dir_489_);
lean_dec_ref(v_self_487_);
v_buildDir_490_ = lean_ctor_get(v_config_488_, 5);
lean_inc_ref(v_buildDir_490_);
v_nativeLibDir_491_ = lean_ctor_get(v_config_488_, 7);
lean_inc_ref(v_nativeLibDir_491_);
lean_dec_ref(v_config_488_);
v___x_492_ = l_System_FilePath_normalize(v_buildDir_490_);
v___x_493_ = l_Lake_joinRelative(v_dir_489_, v___x_492_);
v___x_494_ = l_System_FilePath_normalize(v_nativeLibDir_491_);
v___x_495_ = l_Lake_joinRelative(v___x_493_, v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_sharedLibDir(lean_object* v_self_496_){
_start:
{
lean_object* v_config_497_; lean_object* v_dir_498_; lean_object* v_buildDir_499_; lean_object* v_nativeLibDir_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_config_497_ = lean_ctor_get(v_self_496_, 6);
lean_inc_ref(v_config_497_);
v_dir_498_ = lean_ctor_get(v_self_496_, 4);
lean_inc_ref(v_dir_498_);
lean_dec_ref(v_self_496_);
v_buildDir_499_ = lean_ctor_get(v_config_497_, 5);
lean_inc_ref(v_buildDir_499_);
v_nativeLibDir_500_ = lean_ctor_get(v_config_497_, 7);
lean_inc_ref(v_nativeLibDir_500_);
lean_dec_ref(v_config_497_);
v___x_501_ = l_System_FilePath_normalize(v_buildDir_499_);
v___x_502_ = l_Lake_joinRelative(v_dir_498_, v___x_501_);
v___x_503_ = l_System_FilePath_normalize(v_nativeLibDir_500_);
v___x_504_ = l_Lake_joinRelative(v___x_502_, v___x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_binDir(lean_object* v_self_505_){
_start:
{
lean_object* v_config_506_; lean_object* v_dir_507_; lean_object* v_buildDir_508_; lean_object* v_binDir_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v_config_506_ = lean_ctor_get(v_self_505_, 6);
lean_inc_ref(v_config_506_);
v_dir_507_ = lean_ctor_get(v_self_505_, 4);
lean_inc_ref(v_dir_507_);
lean_dec_ref(v_self_505_);
v_buildDir_508_ = lean_ctor_get(v_config_506_, 5);
lean_inc_ref(v_buildDir_508_);
v_binDir_509_ = lean_ctor_get(v_config_506_, 8);
lean_inc_ref(v_binDir_509_);
lean_dec_ref(v_config_506_);
v___x_510_ = l_System_FilePath_normalize(v_buildDir_508_);
v___x_511_ = l_Lake_joinRelative(v_dir_507_, v___x_510_);
v___x_512_ = l_System_FilePath_normalize(v_binDir_509_);
v___x_513_ = l_Lake_joinRelative(v___x_511_, v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_irDir(lean_object* v_self_514_){
_start:
{
lean_object* v_config_515_; lean_object* v_dir_516_; lean_object* v_buildDir_517_; lean_object* v_irDir_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_config_515_ = lean_ctor_get(v_self_514_, 6);
lean_inc_ref(v_config_515_);
v_dir_516_ = lean_ctor_get(v_self_514_, 4);
lean_inc_ref(v_dir_516_);
lean_dec_ref(v_self_514_);
v_buildDir_517_ = lean_ctor_get(v_config_515_, 5);
lean_inc_ref(v_buildDir_517_);
v_irDir_518_ = lean_ctor_get(v_config_515_, 9);
lean_inc_ref(v_irDir_518_);
lean_dec_ref(v_config_515_);
v___x_519_ = l_System_FilePath_normalize(v_buildDir_517_);
v___x_520_ = l_Lake_joinRelative(v_dir_516_, v___x_519_);
v___x_521_ = l_System_FilePath_normalize(v_irDir_518_);
v___x_522_ = l_Lake_joinRelative(v___x_520_, v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_libPrefixOnWindows(lean_object* v_self_523_){
_start:
{
lean_object* v_config_524_; uint8_t v_libPrefixOnWindows_525_; 
v_config_524_ = lean_ctor_get(v_self_523_, 6);
v_libPrefixOnWindows_525_ = lean_ctor_get_uint8(v_config_524_, sizeof(void*)*26 + 4);
return v_libPrefixOnWindows_525_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_libPrefixOnWindows___boxed(lean_object* v_self_526_){
_start:
{
uint8_t v_res_527_; lean_object* v_r_528_; 
v_res_527_ = l_Lake_Package_libPrefixOnWindows(v_self_526_);
lean_dec_ref(v_self_526_);
v_r_528_ = lean_box(v_res_527_);
return v_r_528_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f(lean_object* v_self_529_){
_start:
{
lean_object* v_config_530_; lean_object* v_enableArtifactCache_x3f_531_; 
v_config_530_ = lean_ctor_get(v_self_529_, 6);
v_enableArtifactCache_x3f_531_ = lean_ctor_get(v_config_530_, 24);
lean_inc(v_enableArtifactCache_x3f_531_);
return v_enableArtifactCache_x3f_531_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f___boxed(lean_object* v_self_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lake_Package_enableArtifactCache_x3f(v_self_532_);
lean_dec_ref(v_self_532_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f(lean_object* v_self_534_){
_start:
{
lean_object* v_config_535_; lean_object* v_restoreAllArtifacts_x3f_536_; 
v_config_535_ = lean_ctor_get(v_self_534_, 6);
v_restoreAllArtifacts_x3f_536_ = lean_ctor_get(v_config_535_, 25);
lean_inc(v_restoreAllArtifacts_x3f_536_);
return v_restoreAllArtifacts_x3f_536_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts_x3f___boxed(lean_object* v_self_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lake_Package_restoreAllArtifacts_x3f(v_self_537_);
lean_dec_ref(v_self_537_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_cacheScope(lean_object* v_self_539_){
_start:
{
lean_object* v_baseName_540_; uint8_t v___x_541_; lean_object* v___x_542_; 
v_baseName_540_ = lean_ctor_get(v_self_539_, 1);
lean_inc(v_baseName_540_);
lean_dec_ref(v_self_539_);
v___x_541_ = 0;
v___x_542_ = l_Lean_Name_toString(v_baseName_540_, v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(lean_object* v_self_544_){
_start:
{
lean_object* v_origName_545_; lean_object* v_scope_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_origName_545_ = lean_ctor_get(v_self_544_, 3);
lean_inc(v_origName_545_);
v_scope_546_ = lean_ctor_get(v_self_544_, 10);
lean_inc_ref(v_scope_546_);
lean_dec_ref(v_self_544_);
v___x_547_ = ((lean_object*)(l___private_Lake_Config_Package_0__Lake_Package_reservoirScope___closed__0));
v___x_548_ = lean_string_append(v_scope_546_, v___x_547_);
v___x_549_ = 0;
v___x_550_ = l_Lean_Name_toString(v_origName_545_, v___x_549_);
v___x_551_ = lean_string_append(v___x_548_, v___x_550_);
lean_dec_ref(v___x_550_);
v___x_552_ = l_Lake_CacheServiceScope_ofString(v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoirScope_x3f(lean_object* v_self_553_){
_start:
{
lean_object* v_scope_554_; lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v_scope_554_ = lean_ctor_get(v_self_553_, 10);
v___x_555_ = lean_string_utf8_byte_size(v_scope_554_);
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = lean_nat_dec_eq(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(v_self_553_);
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
}
else
{
lean_object* v___x_560_; 
lean_dec_ref(v_self_553_);
v___x_560_ = lean_box(0);
return v___x_560_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(lean_object* v_t_561_, lean_object* v_k_562_){
_start:
{
if (lean_obj_tag(v_t_561_) == 0)
{
lean_object* v_k_563_; lean_object* v_v_564_; lean_object* v_l_565_; lean_object* v_r_566_; uint8_t v___x_567_; 
v_k_563_ = lean_ctor_get(v_t_561_, 1);
v_v_564_ = lean_ctor_get(v_t_561_, 2);
v_l_565_ = lean_ctor_get(v_t_561_, 3);
v_r_566_ = lean_ctor_get(v_t_561_, 4);
v___x_567_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_562_, v_k_563_);
switch(v___x_567_)
{
case 0:
{
v_t_561_ = v_l_565_;
goto _start;
}
case 1:
{
lean_object* v___x_569_; 
lean_inc(v_v_564_);
v___x_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_569_, 0, v_v_564_);
return v___x_569_;
}
default: 
{
v_t_561_ = v_r_566_;
goto _start;
}
}
}
else
{
lean_object* v___x_571_; 
v___x_571_ = lean_box(0);
return v___x_571_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg___boxed(lean_object* v_t_572_, lean_object* v_k_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_572_, v_k_573_);
lean_dec(v_k_573_);
lean_dec(v_t_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object* v_name_575_, lean_object* v_self_576_){
_start:
{
lean_object* v_targetDeclMap_577_; lean_object* v___x_578_; 
v_targetDeclMap_577_ = lean_ctor_get(v_self_576_, 14);
v___x_578_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_targetDeclMap_577_, v_name_575_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f___boxed(lean_object* v_name_579_, lean_object* v_self_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lake_Package_findTargetDecl_x3f(v_name_579_, v_self_580_);
lean_dec_ref(v_self_580_);
lean_dec(v_name_579_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(lean_object* v_00_u03b2_582_, lean_object* v_inst_583_, lean_object* v_t_584_, lean_object* v_k_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_584_, v_k_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___boxed(lean_object* v_00_u03b2_587_, lean_object* v_inst_588_, lean_object* v_t_589_, lean_object* v_k_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(v_00_u03b2_587_, v_inst_588_, v_t_589_, v_k_590_);
lean_dec(v_k_590_);
lean_dec(v_t_589_);
return v_res_591_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(lean_object* v_mod_595_, lean_object* v_as_596_, size_t v_i_597_, size_t v_stop_598_){
_start:
{
uint8_t v___x_599_; 
v___x_599_ = lean_usize_dec_eq(v_i_597_, v_stop_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v_kind_601_; lean_object* v_config_602_; uint8_t v___x_603_; uint8_t v___y_605_; lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_600_ = lean_array_uget_borrowed(v_as_596_, v_i_597_);
v_kind_601_ = lean_ctor_get(v___x_600_, 2);
v_config_602_ = lean_ctor_get(v___x_600_, 3);
v___x_603_ = 1;
v___x_609_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1));
v___x_610_ = lean_name_eq(v_kind_601_, v___x_609_);
if (v___x_610_ == 0)
{
v___y_605_ = v___x_599_;
goto v___jp_604_;
}
else
{
uint8_t v___x_611_; 
v___x_611_ = l_Lake_LeanLibConfig_isLocalModule___redArg(v_mod_595_, v_config_602_);
v___y_605_ = v___x_611_;
goto v___jp_604_;
}
v___jp_604_:
{
if (v___y_605_ == 0)
{
size_t v___x_606_; size_t v___x_607_; 
v___x_606_ = ((size_t)1ULL);
v___x_607_ = lean_usize_add(v_i_597_, v___x_606_);
v_i_597_ = v___x_607_;
goto _start;
}
else
{
return v___x_603_;
}
}
}
else
{
uint8_t v___x_612_; 
v___x_612_ = 0;
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___boxed(lean_object* v_mod_613_, lean_object* v_as_614_, lean_object* v_i_615_, lean_object* v_stop_616_){
_start:
{
size_t v_i_boxed_617_; size_t v_stop_boxed_618_; uint8_t v_res_619_; lean_object* v_r_620_; 
v_i_boxed_617_ = lean_unbox_usize(v_i_615_);
lean_dec(v_i_615_);
v_stop_boxed_618_ = lean_unbox_usize(v_stop_616_);
lean_dec(v_stop_616_);
v_res_619_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_613_, v_as_614_, v_i_boxed_617_, v_stop_boxed_618_);
lean_dec_ref(v_as_614_);
lean_dec(v_mod_613_);
v_r_620_ = lean_box(v_res_619_);
return v_r_620_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isLocalModule(lean_object* v_mod_621_, lean_object* v_self_622_){
_start:
{
lean_object* v_targetDecls_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v_targetDecls_623_ = lean_ctor_get(v_self_622_, 13);
v___x_624_ = lean_unsigned_to_nat(0u);
v___x_625_ = lean_array_get_size(v_targetDecls_623_);
v___x_626_ = lean_nat_dec_lt(v___x_624_, v___x_625_);
if (v___x_626_ == 0)
{
return v___x_626_;
}
else
{
if (v___x_626_ == 0)
{
return v___x_626_;
}
else
{
size_t v___x_627_; size_t v___x_628_; uint8_t v___x_629_; 
v___x_627_ = ((size_t)0ULL);
v___x_628_ = lean_usize_of_nat(v___x_625_);
v___x_629_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_621_, v_targetDecls_623_, v___x_627_, v___x_628_);
return v___x_629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isLocalModule___boxed(lean_object* v_mod_630_, lean_object* v_self_631_){
_start:
{
uint8_t v_res_632_; lean_object* v_r_633_; 
v_res_632_ = l_Lake_Package_isLocalModule(v_mod_630_, v_self_631_);
lean_dec_ref(v_self_631_);
lean_dec(v_mod_630_);
v_r_633_ = lean_box(v_res_632_);
return v_r_633_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(lean_object* v_mod_634_, lean_object* v_as_635_, size_t v_i_636_, size_t v_stop_637_){
_start:
{
uint8_t v___x_638_; 
v___x_638_ = lean_usize_dec_eq(v_i_636_, v_stop_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; lean_object* v_kind_640_; lean_object* v_config_641_; uint8_t v___x_642_; uint8_t v___y_644_; lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_639_ = lean_array_uget_borrowed(v_as_635_, v_i_636_);
v_kind_640_ = lean_ctor_get(v___x_639_, 2);
v_config_641_ = lean_ctor_get(v___x_639_, 3);
v___x_642_ = 1;
v___x_655_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1));
v___x_656_ = lean_name_eq(v_kind_640_, v___x_655_);
if (v___x_656_ == 0)
{
goto v___jp_648_;
}
else
{
uint8_t v___x_657_; 
v___x_657_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_634_, v_config_641_);
if (v___x_657_ == 0)
{
goto v___jp_648_;
}
else
{
v___y_644_ = v___x_657_;
goto v___jp_643_;
}
}
v___jp_643_:
{
if (v___y_644_ == 0)
{
size_t v___x_645_; size_t v___x_646_; 
v___x_645_ = ((size_t)1ULL);
v___x_646_ = lean_usize_add(v_i_636_, v___x_645_);
v_i_636_ = v___x_646_;
goto _start;
}
else
{
return v___x_642_;
}
}
v___jp_648_:
{
lean_object* v_kind_649_; lean_object* v_config_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v_kind_649_ = lean_ctor_get(v___x_639_, 2);
v_config_650_ = lean_ctor_get(v___x_639_, 3);
v___x_651_ = l_Lake_LeanExe_keyword;
v___x_652_ = lean_name_eq(v_kind_649_, v___x_651_);
if (v___x_652_ == 0)
{
v___y_644_ = v___x_638_;
goto v___jp_643_;
}
else
{
lean_object* v_root_653_; uint8_t v___x_654_; 
v_root_653_ = lean_ctor_get(v_config_650_, 2);
v___x_654_ = lean_name_eq(v_root_653_, v_mod_634_);
v___y_644_ = v___x_654_;
goto v___jp_643_;
}
}
}
else
{
uint8_t v___x_658_; 
v___x_658_ = 0;
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0___boxed(lean_object* v_mod_659_, lean_object* v_as_660_, lean_object* v_i_661_, lean_object* v_stop_662_){
_start:
{
size_t v_i_boxed_663_; size_t v_stop_boxed_664_; uint8_t v_res_665_; lean_object* v_r_666_; 
v_i_boxed_663_ = lean_unbox_usize(v_i_661_);
lean_dec(v_i_661_);
v_stop_boxed_664_ = lean_unbox_usize(v_stop_662_);
lean_dec(v_stop_662_);
v_res_665_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_659_, v_as_660_, v_i_boxed_663_, v_stop_boxed_664_);
lean_dec_ref(v_as_660_);
lean_dec(v_mod_659_);
v_r_666_ = lean_box(v_res_665_);
return v_r_666_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isBuildableModule(lean_object* v_mod_667_, lean_object* v_self_668_){
_start:
{
lean_object* v_targetDecls_669_; lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v_targetDecls_669_ = lean_ctor_get(v_self_668_, 13);
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = lean_array_get_size(v_targetDecls_669_);
v___x_672_ = lean_nat_dec_lt(v___x_670_, v___x_671_);
if (v___x_672_ == 0)
{
return v___x_672_;
}
else
{
if (v___x_672_ == 0)
{
return v___x_672_;
}
else
{
size_t v___x_673_; size_t v___x_674_; uint8_t v___x_675_; 
v___x_673_ = ((size_t)0ULL);
v___x_674_ = lean_usize_of_nat(v___x_671_);
v___x_675_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_667_, v_targetDecls_669_, v___x_673_, v___x_674_);
return v___x_675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isBuildableModule___boxed(lean_object* v_mod_676_, lean_object* v_self_677_){
_start:
{
uint8_t v_res_678_; lean_object* v_r_679_; 
v_res_678_ = l_Lake_Package_isBuildableModule(v_mod_676_, v_self_677_);
lean_dec_ref(v_self_677_);
lean_dec(v_mod_676_);
v_r_679_ = lean_box(v_res_678_);
return v_r_679_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_clean(lean_object* v_self_680_){
_start:
{
lean_object* v_config_682_; lean_object* v_dir_683_; lean_object* v_buildDir_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_config_682_ = lean_ctor_get(v_self_680_, 6);
lean_inc_ref(v_config_682_);
v_dir_683_ = lean_ctor_get(v_self_680_, 4);
lean_inc_ref(v_dir_683_);
lean_dec_ref(v_self_680_);
v_buildDir_684_ = lean_ctor_get(v_config_682_, 5);
lean_inc_ref(v_buildDir_684_);
lean_dec_ref(v_config_682_);
v___x_685_ = l_System_FilePath_normalize(v_buildDir_684_);
v___x_686_ = l_Lake_joinRelative(v_dir_683_, v___x_685_);
v___x_687_ = l_Lake_removeDirAllIfExists(v___x_686_);
lean_dec_ref(v___x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_clean___boxed(lean_object* v_self_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lake_Package_clean(v_self_688_);
return v_res_690_;
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
